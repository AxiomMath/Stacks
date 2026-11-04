module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.IteratedRestrictionSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingAffineLocalization

/-!
# A splitting over an affine étale neighbourhood, as a groupoid of finite shape

The proof of **Stacks 0DU4** applies **Stacks 0DTE** to the restriction of the groupoid
`R = U ×_𝒳 U` of a flat, locally quasi-finite chart with affine `U`. It then takes the splitting
`P ⊆ R|_{U''}` as the groupoid presenting the étale neighbourhood `[U''/P]`. This file proves the
groupoid-scheme part of that step:

* the splitting is produced for every realization of the restriction of `R` along the
  *composite* `U'' ⟶ U`, which is how the tag reads `R|_{U''}`, and not only for the two-step
  restriction `(R|_{U'})|_{U''}` that Stacks 0DTE delivers;
* the splitting is a groupoid scheme of the shape of clause (3) of Stacks 0DU4: both structure
  schemes affine, source and target finite, flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.isIso_stabilizerMap`: a morphism of groupoid schemes which is an isomorphism
  on objects and on arrows induces an isomorphism of stabilizers.
* `Stacks.Groupoids.GroupoidScheme.Splitting.transport`: a splitting transports along a morphism
  of groupoid schemes which is an isomorphism on arrows and an equality on objects.
* `AlgebraicGeometry.GroupoidScheme.isSplitAt_of_iteratedRestriction'`: a realization of
  `G|_{U''}` is split over a point of `U''` whenever a realization of `(G|_{U'})|_{U''}` is.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isFinite_flat_splitting`: **Stacks 0DTE at a
  groupoid scheme with affine object scheme, whose source and target are separated, flat and
  locally of finite presentation and whose source is locally quasi-finite, with finitely many
  stabilizer points over `u`.** The splitting is delivered as a groupoid scheme of the shape of
  clause (3) of Stacks 0DU4, included in the restriction along the composite by the identity on
  objects, and containing the arrow of every stabilizer point over the new point.

## Implementation notes

The source's hypothesis that `s` is quasi-finite at the stabilizer points over `u` (Situation
0DTB) follows from local quasi-finiteness of `s`, and that is the form in which the chart
groupoid of the proof of Stacks 0DU4 supplies it.

## References

* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTE](https://stacks.math.columbia.edu/tag/0DTE)
* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace AlgebraicGeometry

/-- A morphism of groupoid schemes which is an isomorphism on objects and on arrows induces an
isomorphism of stabilizers: the map of stabilizers is the map of fibre products induced by three
isomorphisms. -/
theorem isIso_stabilizerMap {S : Scheme.{u}} {G G' : Stacks.Groupoids.GroupoidScheme S}
    (F : Stacks.Groupoids.GroupoidScheme.Hom G' G) [IsIso F.mapArrows] [IsIso F.mapObjects] :
    IsIso (stabilizerMap F) := by
  have e₁ : sourceTarget G' ≫ (F.mapObjects ⊗ₘ F.mapObjects) = F.mapArrows ≫ sourceTarget G := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [sourceTarget, F.map_target, F.map_source]
  have e₂ : diagonal G' ≫ (F.mapObjects ⊗ₘ F.mapObjects) = F.mapObjects ≫ diagonal G := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [diagonal]
  have h : stabilizerMap F = pullback.map (sourceTarget G') (diagonal G') (sourceTarget G)
      (diagonal G) F.mapArrows F.mapObjects (F.mapObjects ⊗ₘ F.mapObjects) e₁ e₂ := by
    apply pullback.hom_ext
    · rw [stabilizerMap_fst, pullback.lift_fst]
    · rw [stabilizerMap_snd, pullback.lift_snd]
  rw [h]
  infer_instance

end AlgebraicGeometry

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- Transport of a splitting along a morphism of groupoid schemes which is an isomorphism on
arrow schemes and is given on objects by an equality of object schemes. The transported
subgroupoid is the original one, with its inclusion composed with the morphism; a point of the
stabilizer of the target over the transported point is the image of a point of the stabilizer of
the source over the original point, because the map of stabilizers is an isomorphism. -/
def Splitting.transport {K L : GroupoidScheme S} {u : K.objects.left} (P : Splitting K u)
    (Φ : Hom K L) (e : K.objects = L.objects) (hΦ : Φ.mapObjects = eqToHom e)
    [IsIso Φ.mapArrows] : Splitting L ((eqToHom e).left.base u) where
  toOpenFiniteSubgroupoid := P.toOpenFiniteSubgroupoid.transport Φ e hΦ
  contains_stabilizer := by
    intro x hx
    have : IsIso Φ.mapObjects := by
      rw [hΦ]
      infer_instance
    have := AlgebraicGeometry.isIso_stabilizerMap Φ
    let y := (inv (AlgebraicGeometry.stabilizerMap Φ)).left.base x
    have hyx : (AlgebraicGeometry.stabilizerMap Φ).left.base y = x := by
      simp only [y, ← Scheme.Hom.comp_apply, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left]
      rfl
    have hy : (AlgebraicGeometry.stabilizer K).hom.base y = u := by
      have h1 := congrArg (fun k => k.base y)
        (AlgebraicGeometry.stabilizerMap_left_comp_hom Φ)
      simp only [Scheme.Hom.comp_apply] at h1
      rw [hyx, hx, hΦ] at h1
      have h2 := congrArg (eqToHom e.symm).left.base h1
      rwa [over_eqToHom_apply_symm, over_eqToHom_apply_symm, eq_comm] at h2
    obtain ⟨p, hp⟩ := P.contains_stabilizer y hy
    refine ⟨p, ?_⟩
    change (P.inclusion.mapArrows ≫ Φ.mapArrows).left.base p = _
    rw [Over.comp_left, Scheme.Hom.comp_apply, hp, ← hyx]
    have h3 := congrArg (fun k => k.base y)
      (AlgebraicGeometry.stabilizerMap_left_comp_stabilizerArrow Φ)
    simpa only [Scheme.Hom.comp_apply] using h3.symm

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {H : Stacks.Groupoids.GroupoidScheme S} {U' U'' : Over S}
  {g : U' ⟶ H.objects} (R' : Restriction H g) {j : U'' ⟶ R'.groupoid.objects}
  (R'' : Restriction R'.groupoid j) (R''' : Restriction H (j ≫ R'.hom.mapObjects))

/-- A realization of `G|_{U''}` is split over a point of `U''` whenever a realization of
`(G|_{U'})|_{U''}` is split over that same point. -/
theorem isSplitAt_of_iteratedRestriction' (u'' : U''.left)
    (h : Stacks.Groupoids.GroupoidScheme.IsSplitAt R''.groupoid
      ((eqToHom R''.objects_eq.symm).left.base u'')) :
    Stacks.Groupoids.GroupoidScheme.IsSplitAt R'''.groupoid
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


namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- An open finite subgroupoid of a groupoid scheme with affine object scheme and flat, locally
finitely presented source and target has affine object and arrow schemes, and flat, locally
finitely presented source and target. -/
private theorem OpenFiniteSubgroupoid.isAffine_flat_locallyOfFinitePresentation
    {K : GroupoidScheme S}
    (P : OpenFiniteSubgroupoid K) [IsAffine K.objects.left] [Flat K.source.left]
    [LocallyOfFinitePresentation K.source.left] [Flat K.target.left]
    [LocallyOfFinitePresentation K.target.left] :
    IsAffine P.subgroupoid.objects.left ∧ IsAffine P.subgroupoid.arrows.left ∧
      Flat P.subgroupoid.source.left ∧ LocallyOfFinitePresentation P.subgroupoid.source.left ∧
      Flat P.subgroupoid.target.left ∧ LocallyOfFinitePresentation P.subgroupoid.target.left := by
  have key {σ : P.subgroupoid.arrows ⟶ P.subgroupoid.objects} {τ : K.arrows ⟶ K.objects}
      (h : P.inclusion.mapArrows ≫ τ = σ ≫ P.inclusion.mapObjects) :
      σ.left = P.inclusion.mapArrows.left ≫ τ.left ≫ (eqToHom P.objects_eq.symm).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, h]
    simp [P.mapObjects_eq]
  have hs := key P.inclusion.map_source
  have ht := key P.inclusion.map_target
  have : IsIso (eqToHom P.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom P.objects_eq.symm)))
  have := P.arrows_open
  have := P.source_finite
  have : IsAffine P.subgroupoid.objects.left := by
    rw [P.objects_eq]
    infer_instance
  refine ⟨inferInstance, isAffine_of_isAffineHom P.subgroupoid.source.left, ?_, ?_, ?_, ?_⟩ <;>
    first | (rw [hs]; infer_instance) | (rw [ht]; infer_instance)

/-- **Stacks 0DTE, with the splitting delivered as a groupoid scheme of the shape of clause (3)
of Stacks 0DU4.** Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine, with `s`
and `t` separated, flat and locally of finite presentation and with `s` locally quasi-finite, and
let `u ∈ U` be a point over which the stabilizer has finitely many points. Then there are an
affine `U''`, an étale `g : U'' ⟶ U` and a point `u''` over `u` with `κ(u) = κ(u'')` such that
every groupoid scheme realizing the restriction `R|_{U''}` along `g` has flat, locally finitely
presented source and target and contains a splitting over `u''`: a groupoid scheme `P` on the
same object scheme, included by an open immersion on arrows and the identity on objects,
containing the arrow of every stabilizer point over `u''`, with both
structure schemes affine and with source and target finite, flat and locally of finite
presentation. -/
theorem exists_isAffine_isFinite_flat_splitting (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    [IsAffine G.objects.left]
    [AlgebraicGeometry.IsSeparated G.source.left] [AlgebraicGeometry.IsSeparated G.target.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left]
    (hfin : Set.Finite {x : (AlgebraicGeometry.stabilizer G).left |
      (AlgebraicGeometry.stabilizer G).hom x = u}) :
    ∃ (U'' : Over S) (g : U'' ⟶ G.objects) (u'' : U''.left),
      IsAffine U''.left ∧ Etale g.left ∧ g.left.base u'' = u ∧
      IsIso (g.left.residueFieldMap u'') ∧
      ∀ R : AlgebraicGeometry.GroupoidScheme.Restriction G g,
        Flat R.groupoid.source.left ∧ LocallyOfFinitePresentation R.groupoid.source.left ∧
        Flat R.groupoid.target.left ∧ LocallyOfFinitePresentation R.groupoid.target.left ∧
        ∃ (H : GroupoidScheme S) (φ : GroupoidScheme.Hom H R.groupoid),
          (∃ hobj : H.objects = R.groupoid.objects, φ.mapObjects = eqToHom hobj) ∧
          AlgebraicGeometry.IsOpenImmersion φ.mapArrows.left ∧
          (∀ x : (AlgebraicGeometry.stabilizer R.groupoid).left,
            (AlgebraicGeometry.stabilizer R.groupoid).hom.base x =
                (eqToHom R.objects_eq.symm).left.base u'' →
              ∃ p : H.arrows.left,
                φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow R.groupoid).base x) ∧
          IsAffine H.objects.left ∧ IsAffine H.arrows.left ∧
          AlgebraicGeometry.IsFinite H.source.left ∧ Flat H.source.left ∧
          LocallyOfFinitePresentation H.source.left ∧
          AlgebraicGeometry.IsFinite H.target.left ∧ Flat H.target.left ∧
          LocallyOfFinitePresentation H.target.left := by
  let D : AlgebraicGeometry.Space.SplittingSituation.{u} :=
    { S := S
      groupoid := G
      u := u
      stabilizer_finite := hfin
      source_quasiFiniteAt := fun _ _ => (AlgebraicGeometry.forall_quasiFiniteAt_iff
        G.source.left).mpr ⟨inferInstance, inferInstance⟩ _ }
  have : IsAffine D.groupoid.objects.left := inferInstanceAs (IsAffine G.objects.left)
  have : Flat D.groupoid.source.left := inferInstanceAs (Flat G.source.left)
  have : LocallyOfFinitePresentation D.groupoid.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.source.left)
  have : Flat D.groupoid.target.left := inferInstanceAs (Flat G.target.left)
  have : LocallyOfFinitePresentation D.groupoid.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.target.left)
  obtain ⟨U', gp, R', U'', j, u'', haff, -, het, hbase, hres, hsplit⟩ :=
    exists_isAffine_isSplitAt D C hS hU hR hP hK
  refine ⟨U'', j ≫ R'.hom.mapObjects, u'', haff, het, hbase, hres, fun R => ?_⟩
  have : IsAffine R.groupoid.objects.left := by rwa [R.objects_eq]
  have hsrc : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsStableUnderComposition], P G.source.left → P (j ≫ R'.hom.mapObjects).left →
      P R.groupoid.source.left ∧ P R.groupoid.target.left := by
    intro P _ _ hs hg
    have h := AlgebraicGeometry.overFibreProduct_comp (pullback.snd (j ≫ R'.hom.mapObjects)
      G.target) G.source (AlgebraicGeometry.overFibreProduct_snd _ G.target hg) hs
    exact ⟨AlgebraicGeometry.restriction_source_mem G _ R P h,
      AlgebraicGeometry.restriction_target_mem G _ R P h⟩
  obtain ⟨h1, h2⟩ := hsrc @Flat inferInstance inferInstance
  obtain ⟨h3, h4⟩ := hsrc @LocallyOfFinitePresentation inferInstance inferInstance
  obtain ⟨P⟩ := AlgebraicGeometry.GroupoidScheme.isSplitAt_of_iteratedRestriction' R'
    (AlgebraicGeometry.GroupoidScheme.restrict R'.groupoid j) R u''
    (hsplit (AlgebraicGeometry.GroupoidScheme.restrict R'.groupoid j))
  obtain ⟨hoa, haa, hsf, hsl, htf, htl⟩ :=
    P.toOpenFiniteSubgroupoid.isAffine_flat_locallyOfFinitePresentation
  exact ⟨h1, h3, h2, h4, P.subgroupoid, P.inclusion, ⟨P.objects_eq, P.mapObjects_eq⟩,
    P.arrows_open, P.contains_stabilizer, hoa, haa, P.source_finite, hsf, hsl, P.target_finite,
    htf, htl⟩

end Stacks.Groupoids.GroupoidScheme


namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- **An arrow with source and target a point over which `H` contains the stabilizer lies in
`H`.** Let `φ : H ⟶ K` be a morphism of groupoid schemes which is an open immersion on arrows,
and suppose the image of `φ` contains the arrow of every stabilizer point of `K` over `u'`. Let
`a : W ⟶ U` be a generalized point of the object scheme all of whose points map to `u'`, and let
`r : W ⟶ R` be a generalized arrow with source and target `a`. Then `r` factors through `φ`.

The pair `(r, a)` is a generalized point of the stabilizer, which lies over `u'` at every point
of `W`; so every point of `r` is the arrow of a stabilizer point over `u'`, hence in the image of
the open immersion `φ`, and `r` lifts. -/
theorem exists_comp_mapArrows_eq_of_stabilizer_le {K H : GroupoidScheme S} (φ : Hom H K)
    (hφ : AlgebraicGeometry.IsOpenImmersion φ.mapArrows.left) {u' : K.objects.left}
    (hstab : ∀ y : (AlgebraicGeometry.stabilizer K).left,
      (AlgebraicGeometry.stabilizer K).hom.base y = u' →
        ∃ p : H.arrows.left,
          φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow K).base y)
    {W : Over S} (a : W ⟶ K.objects) (ha : ∀ w, a.left.base w = u') (r : W ⟶ K.arrows)
    (hs : r ≫ K.source = a) (ht : r ≫ K.target = a) :
    ∃ h : W ⟶ H.arrows, h ≫ φ.mapArrows = r := by
  have hw : r ≫ AlgebraicGeometry.sourceTarget K = a ≫ AlgebraicGeometry.diagonal K := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [AlgebraicGeometry.sourceTarget, AlgebraicGeometry.diagonal, hs, ht]
  let l : W ⟶ AlgebraicGeometry.stabilizerOverBase K := pullback.lift r a hw
  have hrange : Set.range r.left.base ⊆ Set.range φ.mapArrows.left.base := by
    rintro _ ⟨w, rfl⟩
    have hy : (AlgebraicGeometry.stabilizer K).hom.base (l.left.base w) = u' := by
      have h1 : (l ≫ pullback.snd (AlgebraicGeometry.sourceTarget K)
          (AlgebraicGeometry.diagonal K)).left.base w = a.left.base w := by
        rw [pullback.lift_snd]
      rw [Over.comp_left, Scheme.Hom.comp_apply] at h1
      exact h1.trans (ha w)
    obtain ⟨p, hp⟩ := hstab _ hy
    refine ⟨p, hp.trans ?_⟩
    have h2 : (l ≫ pullback.fst (AlgebraicGeometry.sourceTarget K)
        (AlgebraicGeometry.diagonal K)).left.base w = r.left.base w := by
      rw [pullback.lift_fst]
    rwa [Over.comp_left, Scheme.Hom.comp_apply] at h2
  refine ⟨Over.homMk (AlgebraicGeometry.IsOpenImmersion.lift φ.mapArrows.left r.left hrange) ?_,
    Over.OverMorphism.ext (AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← Over.w φ.mapArrows, ← Category.assoc, AlgebraicGeometry.IsOpenImmersion.lift_fac]
  exact Over.w r

end Stacks.Groupoids.GroupoidScheme

end
