module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relation is the kernel pair of the projection onto its quotient

Let `j : R ⟶ U ×_S U` be an equivalence relation of schemes over `S` and let `F : C ⥤ Over S`
present a site of `S`-schemes.  Then `R` is the kernel pair of the projection of `U` onto the
quotient: the square formed by the target and the source of `j` and by two copies of that
projection is Cartesian, both for the quotient presheaf and — as soon as the functors of points
of `R` and of `U` are sheaves — for the quotient sheaf.

This is the converse direction of the representability criterion of Stacks 03C5: where that
criterion deduces `U/R ≅ h_M` from `R = U ×_M U`, this says that the relation is recovered as
the kernel pair of the projection onto `U/R` itself.

## Main results

* `Stacks.Groupoids.isPullback_toQuotientPresheaf_self` for the quotient presheaf, with no
  sheaf hypothesis.
* `Stacks.Groupoids.isPullback_toQuotientSheaf_self` for the quotient sheaf.

## References

* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- **The relation is the kernel pair of the projection onto the quotient presheaf.** For an
equivalence relation `j : R ⟶ U ×_S U` over `S`, the square formed by the target and the source
of `j` and by two copies of the projection of the functor of points of `U` onto the quotient
presheaf is Cartesian.  No sheaf hypothesis is needed. -/
@[sga "3 IV 4.4.9" "special case"]
theorem isPullback_toQuotientPresheaf_self (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) [IsEquivalenceRelation j.target j.source] :
    IsPullback (targetMap F j) (sourceMap F j) (toQuotientPresheaf F j)
      (toQuotientPresheaf F j) := by
  have : Mono j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).1
  have hj : IsPreEquivalenceRelation j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).2
  set q := toQuotientPresheaf F j with hqdef
  set tt := targetMap F j with httdef
  set ss := sourceMap F j with hssdef
  have hcomm : tt ≫ q = ss ≫ q := (coequalizer.condition ss tt).symm
  let c : PullbackCone q q := PullbackCone.mk tt ss hcomm
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits c
    intro T'
    let T := T'.unop
    let ct : PullbackCone (q.app T') (q.app T') :=
      PullbackCone.mk (tt.app T') (ss.app T') (by
        simpa [NatTrans.comp_app, ConcreteCategory.comp_apply] using congr_app hcomm T')
    have hbije : Function.Bijective ct.toPullbackObj := by
      constructor
      · intro x y hxy
        have h1 : tt.app T' x = tt.app T' y := congrArg (fun p => p.1.1) hxy
        have h2 : ss.app T' x = ss.app T' y := congrArg (fun p => p.1.2) hxy
        refine (cancel_mono j).mp (prod.hom_ext ?_ ?_)
        · exact (Category.assoc x j prod.fst).trans
            (h1.trans (Category.assoc y j prod.fst).symm)
        · exact (Category.assoc x j prod.snd).trans
            (h2.trans (Category.assoc y j prod.snd).symm)
      · rintro ⟨⟨a, b⟩, hab⟩
        obtain ⟨r, hrt, hrs⟩ :=
          (toQuotientPresheaf_apply_eq_iff_related F j hj T a b).mp hab
        refine ⟨r, Subtype.ext (Prod.ext ?_ ?_)⟩
        · change tt.app T' r = a
          simpa [tt, targetMap, points] using hrt
        · change ss.app T' r = b
          simpa [ss, sourceMap, points] using hrs
    have hct : IsLimit ct := (PullbackCone.isLimitEquivBijective ct).2 hbije
    exact (IsLimit.equivOfNatIsoOfIso (cospanCompIso ((evaluation Cᵒᵖ (Type u)).obj T') q q)
      (((evaluation Cᵒᵖ (Type u)).obj T').mapCone c) ct
      (WalkingCospan.ext (Iso.refl _) (by
        change tt.app T' = 𝟙 _ ≫ tt.app T'
        simp) (by
        change ss.app T' = 𝟙 _ ≫ ss.app T'
        simp))).symm hct
  exact IsPullback.of_isLimit hc

/-- **The relation is the kernel pair of the projection onto the quotient sheaf.** For an
equivalence relation `j : R ⟶ U ×_S U` over `S` whose functors of points of `R` and of `U` are
sheaves, the square formed by the target and the source of `j` and by two copies of the
projection of the functor of points of `U` onto the quotient sheaf is Cartesian. -/
@[sga "3 IV 4.4.9" "partial"]
theorem isPullback_toQuotientSheaf_self (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] (hR : Presheaf.IsSheaf J (points F R))
    (hU : Presheaf.IsSheaf J (points F U)) :
    IsPullback (targetMap F j) (sourceMap F j) (toQuotientSheaf J F j)
      (toQuotientSheaf J F j) := by
  let PR := points F R
  let PU := points F U
  let q := toQuotientPresheaf F j
  let tt := targetMap F j
  let ss := sourceMap F j
  let sh := presheafToSheaf J (Type u)
  let forgetSheaf := sheafToPresheaf J (Type u)
  have hpresheaf' : IsPullback (forgetSheaf.map (sh.map tt)) (forgetSheaf.map (sh.map ss))
      (forgetSheaf.map (sh.map q)) (forgetSheaf.map (sh.map q)) :=
    ((isPullback_toQuotientPresheaf_self F j).map sh).map forgetSheaf
  let eR := isoSheafify J hR
  let eU := isoSheafify J hU
  have hInvUnitR : eR.symm.hom ≫ toSheafify J PR = 𝟙 _ := by
    rw [← isoSheafify_hom J hR]
    exact eR.inv_hom_id
  have hInvUnitU : eU.symm.hom ≫ toSheafify J PU = 𝟙 _ := by
    rw [← isoSheafify_hom J hU]
    exact eU.inv_hom_id
  have hUnitInvU : toSheafify J PU ≫ eU.symm.hom = 𝟙 _ := by
    rw [← isoSheafify_hom J hU]
    exact eU.hom_inv_id
  have hstep : ∀ k : PR ⟶ PU, sheafifyMap J k ≫ eU.symm.hom = eR.symm.hom ≫ k := by
    intro k
    have hn : k ≫ toSheafify J PU = toSheafify J PR ≫ sheafifyMap J k := by
      simp [PR, PU]
    calc
      sheafifyMap J k ≫ eU.symm.hom =
          (eR.symm.hom ≫ toSheafify J PR) ≫ sheafifyMap J k ≫ eU.symm.hom := by
        rw [hInvUnitR, Category.id_comp]
      _ = eR.symm.hom ≫ (k ≫ toSheafify J PU) ≫ eU.symm.hom := by
        rw [hn]
        simp only [Category.assoc]
      _ = eR.symm.hom ≫ k ≫ toSheafify J PU ≫ eU.symm.hom := by
        simp only [Category.assoc]
      _ = eR.symm.hom ≫ k := by rw [hUnitInvU, Category.comp_id]
  apply IsPullback.of_iso hpresheaf' eR.symm eU.symm eU.symm (Iso.refl _)
  · exact hstep tt
  · exact hstep ss
  · change sheafifyMap J q ≫ 𝟙 _ = eU.symm.hom ≫ q ≫ toSheafify J (quotientPresheaf F j)
    rw [toSheafify_naturality J q, ← Category.assoc, hInvUnitU, Category.id_comp,
      Category.comp_id]
  · change sheafifyMap J q ≫ 𝟙 _ = eU.symm.hom ≫ q ≫ toSheafify J (quotientPresheaf F j)
    rw [toSheafify_naturality J q, ← Category.assoc, hInvUnitU, Category.id_comp,
      Category.comp_id]

end Stacks.Groupoids

end
