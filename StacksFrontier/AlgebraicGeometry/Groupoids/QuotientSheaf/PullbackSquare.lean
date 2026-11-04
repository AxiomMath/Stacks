module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafEquality

/-!
# Cartesian squares of quotient sheaves of equivalence relations

Let `j : R ⟶ U ×_S U` and `j' : R' ⟶ U' ×_S U'` be equivalence relations over `S` and let
`(r, f)` be a morphism from `j` to `j'` whose square on source maps is cartesian. Then the
square formed by the two projections onto the quotients and by `f` is again cartesian: `U` is
the fibre product of `U'` and `U/R` over `U'/R'`.

## Main results

* `Stacks.Groupoids.eq_of_rel_of_map_eq`: over a cartesian square on source maps, two related
  points of `U` with the same image in `U'` are equal.
* `Stacks.Groupoids.isPullback_toQuotientPresheaf` is the statement for quotient presheaves.
* `Stacks.Groupoids.isPullback_toQuotientSheaf` is the statement for quotient sheaves.

## Implementation notes

The site is presented by an arbitrary functor `F : C ⥤ Over S` into `S`-schemes, which covers
the big and small Zariski, étale, fppf, smooth and syntomic sites at once. The square is
expressed in presheaves; because the two functors of points occurring in it are assumed to be
sheaves, this is equivalent to a fibre-product square of sheaves.

## References

* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

/-- Over a cartesian square on the source maps of two equivalence relations, two related
`T`-valued points of `U` with the same image in `U'` are equal. -/
theorem eq_of_rel_of_map_eq {S : Scheme.{u}} {R U R' U' : Over S} (j : PreRelation R U)
    (j' : PreRelation R' U') [IsEquivalenceRelation j.target j.source]
    [IsEquivalenceRelation j'.target j'.source] (r : R ⟶ R') (f : U ⟶ U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hcart : IsPullback r j.source j'.source f) {T : Over S} {a b : T ⟶ U}
    (hrel : j.Rel b a) (hmap : a ≫ f = b ≫ f) : a = b := by
  obtain ⟨q, hqt, hqs⟩ := hrel
  let e : EquivalenceRelation j.target j.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  let e' : EquivalenceRelation j'.target j'.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  have hreflTarget : (a ≫ e.r) ≫ j.target = a := by simp [Category.assoc, e.reflexivity₁]
  have hreflSource : (a ≫ e.r) ≫ j.source = a := by simp [Category.assoc, e.reflexivity₂]
  have htarget : (q ≫ r) ≫ j'.target = ((a ≫ e.r) ≫ r) ≫ j'.target := by
    calc
      (q ≫ r) ≫ j'.target = (q ≫ j.target) ≫ f := by simp [Category.assoc, ht]
      _ = a ≫ f := by rw [hqt, hmap.symm]
      _ = ((a ≫ e.r) ≫ r) ≫ j'.target := by
        rw [Category.assoc, ht, ← Category.assoc, hreflTarget]
  have hsource : (q ≫ r) ≫ j'.source = ((a ≫ e.r) ≫ r) ≫ j'.source := by
    calc
      (q ≫ r) ≫ j'.source = (q ≫ j.source) ≫ f := by simp [Category.assoc, hs]
      _ = a ≫ f := by rw [hqs]
      _ = ((a ≫ e.r) ≫ r) ≫ j'.source := by
        rw [Category.assoc, hs, ← Category.assoc, hreflSource]
  have hq : q = a ≫ e.r :=
    hcart.hom_ext (e'.right_cancellation _ _ htarget hsource) (by rw [hqs, hreflSource])
  calc
    a = (a ≫ e.r) ≫ j.target := hreflTarget.symm
    _ = q ≫ j.target := by rw [← hq]
    _ = b := hqt

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- A cartesian square on the source maps of two equivalence relations induces a cartesian
square on their quotient presheaves. -/
theorem isPullback_toQuotientPresheaf (F : C ⥤ Over S) {R U R' U' : Over S}
    (j : PreRelation R U) (j' : PreRelation R' U')
    [IsEquivalenceRelation j.target j.source] [IsEquivalenceRelation j'.target j'.source]
    (r : R ⟶ R') (f : U ⟶ U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hcart : IsPullback r j.source j'.source f) :
    IsPullback (toQuotientPresheaf F j) (F.op.whiskerLeft (yoneda.map f))
      (quotientPresheafMap F j j' r f hs ht) (toQuotientPresheaf F j') := by
  have hj : IsPreEquivalenceRelation j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).2
  have hj' : IsPreEquivalenceRelation j' :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j').mp inferInstance).2
  let q := toQuotientPresheaf F j
  let q' := toQuotientPresheaf F j'
  let ff := F.op.whiskerLeft (yoneda.map f)
  let m := quotientPresheafMap F j j' r f hs ht
  have hcomm : q ≫ m = ff ≫ q' := by
    dsimp [q, m, ff, q', toQuotientPresheaf, quotientPresheafMap]
    rw [coequalizer.π_desc]
  let c : PullbackCone m q' := PullbackCone.mk q ff hcomm
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits c
    intro T'
    let T := T'.unop
    let ct : PullbackCone (m.app T') (q'.app T') :=
      PullbackCone.mk (q.app T') (ff.app T') (by
        simpa [NatTrans.comp_app, ConcreteCategory.comp_apply] using congr_app hcomm T')
    have hbije : Function.Bijective ct.toPullbackObj := by
      constructor
      · intro x y hxy
        have hp := congrArg Subtype.val hxy
        have hqxy : q.app (op T) x = q.app (op T) y := congrArg Prod.fst hp
        have hfxy : ff.app (op T) x = ff.app (op T) y := congrArg Prod.snd hp
        have hrel := (toQuotientPresheaf_apply_eq_iff_related F j hj T x y).mp hqxy
        exact eq_of_rel_of_map_eq j j' r f hs ht hcart ((hj (F.obj T)).symm hrel)
          (by simpa [ff, points] using hfxy)
      · rintro ⟨⟨z, y⟩, hzy⟩
        have hπsurj : Function.Surjective (q.app (op T)) := by
          apply (CategoryTheory.epi_iff_surjective _).mp
          apply (NatTrans.epi_iff_epi_app q).mp
          infer_instance
        obtain ⟨b, hb⟩ := hπsurj z
        have hmap : q'.app (op T) (ff.app (op T) b) = q'.app (op T) y := by
          calc
            q'.app (op T) (ff.app (op T) b) = m.app (op T) (q.app (op T) b) := by
              simpa [NatTrans.comp_app, ConcreteCategory.comp_apply] using
                (congrArg (fun η => η.app (op T) b) hcomm).symm
            _ = m.app (op T) z := by rw [hb]
            _ = q'.app (op T) y := hzy
        obtain ⟨r', hr's, hr't⟩ := (hj' (F.obj T)).symm
          ((toQuotientPresheaf_apply_eq_iff_related F j' hj' T (ff.app (op T) b) y).mp hmap)
        have hsrc : r' ≫ j'.source = b ≫ f := by simpa [ff, points] using hr't
        let a := hcart.lift r' b (by simp [hsrc])
        refine ⟨a ≫ j.target, Subtype.ext (Prod.ext ?_ ?_)⟩
        · refine Eq.trans ?_ hb
          exact (toQuotientPresheaf_apply_eq_iff_related F j hj T (a ≫ j.target) b).2
            ⟨a, rfl, by simp [a, hcart.lift_snd]⟩
        · show ff.app (op T) (a ≫ j.target) = y
          have htarget : (a ≫ j.target) ≫ f = y := by
            calc
              (a ≫ j.target) ≫ f = a ≫ r ≫ j'.target := by rw [Category.assoc, ← ht]
              _ = (a ≫ r) ≫ j'.target := (Category.assoc _ _ _).symm
              _ = r' ≫ j'.target := by rw [hcart.lift_fst]
              _ = y := hr's
          simpa [ff, points] using htarget
    have hct : IsLimit ct := (PullbackCone.isLimitEquivBijective ct).2 hbije
    exact (IsLimit.equivOfNatIsoOfIso (cospanCompIso ((evaluation Cᵒᵖ (Type u)).obj T') m q')
      (((evaluation Cᵒᵖ (Type u)).obj T').mapCone c) ct
      (WalkingCospan.ext (Iso.refl _) (by
        show q.app T' = 𝟙 _ ≫ q.app T'
        simp) (by
        show ff.app T' = 𝟙 _ ≫ ff.app T'
        simp))).symm hct
  exact IsPullback.of_isLimit hc

/-- A cartesian square on the source maps of two equivalence relations stays cartesian after
passing to quotient sheaves, provided the two functors of points occurring in it are sheaves. -/
theorem isPullback_toQuotientSheaf (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {R U R' U' : Over S} (j : PreRelation R U) (j' : PreRelation R' U')
    [IsEquivalenceRelation j.target j.source] [IsEquivalenceRelation j'.target j'.source]
    (r : R ⟶ R') (f : U ⟶ U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hcart : IsPullback r j.source j'.source f)
    (hU : Presheaf.IsSheaf J (points F U)) (hU' : Presheaf.IsSheaf J (points F U')) :
    IsPullback (toQuotientSheaf J F j) (F.op.whiskerLeft (yoneda.map f))
      (quotientSheafMap J F j j' r f hs ht).hom (toQuotientSheaf J F j') := by
  let P := points F U
  let P' := points F U'
  let q := toQuotientPresheaf F j
  let q' := toQuotientPresheaf F j'
  let ff := F.op.whiskerLeft (yoneda.map f)
  let m := quotientPresheafMap F j j' r f hs ht
  let sh := presheafToSheaf J (Type u)
  let forgetSheaf := sheafToPresheaf J (Type u)
  have hpresheaf' : IsPullback (forgetSheaf.map (sh.map q)) (forgetSheaf.map (sh.map ff))
      (forgetSheaf.map (sh.map m)) (forgetSheaf.map (sh.map q')) :=
    ((isPullback_toQuotientPresheaf F j j' r f hs ht hcart).map sh).map forgetSheaf
  have hUnit : ∀ {X : Cᵒᵖ ⥤ Type u} (hX : Presheaf.IsSheaf J X),
      (isoSheafify J hX).symm.hom ≫ toSheafify J X = 𝟙 _ ∧
        toSheafify J X ≫ (isoSheafify J hX).symm.hom = 𝟙 _ := fun hX => by
    rw [← isoSheafify_hom J hX]
    exact ⟨(isoSheafify J hX).inv_hom_id, (isoSheafify J hX).hom_inv_id⟩
  have hsq : ∀ {X Y : Cᵒᵖ ⥤ Type u} (hX : Presheaf.IsSheaf J X) (p : X ⟶ Y),
      sheafifyMap J p ≫ 𝟙 _ = (isoSheafify J hX).symm.hom ≫ p ≫ toSheafify J Y := by
    intro X Y hX p
    rw [toSheafify_naturality J p, ← Category.assoc, (hUnit hX).1, Category.id_comp,
      Category.comp_id]
  apply IsPullback.of_iso hpresheaf' (isoSheafify J hU).symm (Iso.refl _)
    (isoSheafify J hU').symm (Iso.refl _)
  · exact hsq hU q
  · show sheafifyMap J ff ≫ (isoSheafify J hU').symm.hom = (isoSheafify J hU).symm.hom ≫ ff
    rw [← Category.comp_id (sheafifyMap J ff), hsq hU ff]
    simp only [Category.assoc, (hUnit hU').2, Category.comp_id]
  · rfl
  · exact hsq hU' q'

end Stacks.Groupoids

end
