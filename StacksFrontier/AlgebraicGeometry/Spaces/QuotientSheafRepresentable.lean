module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# A criterion for a quotient sheaf to be represented by a scheme

Let `j : R ⟶ U ⨯ U` be a pre-relation on schemes over `S` and let `f : U ⟶ M` be a map which
equalizes the two legs of `j`. If `f` induces a surjection of sheaves on the functors of points,
and if `j` induces a surjection of sheaves onto the functor of points of the relation `U ×_M U` cut
out by `f`, then `M` represents the quotient sheaf `U/R`.

## Main results

* `Stacks.Groupoids.quotientSheaf_isRepresentedBy_of_locallySurjective`: the descent of `f` to the
  quotient sheaf of `j` is an isomorphism onto the functor of points of `M`.

## References

* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

/-- The descent of a map `f : U ⟶ M` equalizing a pre-relation `j` to a map from the quotient
presheaf of `j` to the functor of points of `M`. -/
private noncomputable def quotientToPoints {S : Scheme.{u}} {C : Type v}
    [Category.{w} C] (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M)
    (hf : j.target ≫ f = j.source ≫ f) :
    quotientPresheaf F j ⟶ points F M :=
  coequalizer.desc (F.op.whiskerLeft (yoneda.map f)) (by
    ext X x
    change x ≫ j.source ≫ f = x ≫ j.target ≫ f
    exact congrArg (fun k => x ≫ k) hf.symm)

/-- The descended map agrees with `f` on the functor of points of `U`. -/
private theorem toQuotientPresheaf_quotientToPoints {S : Scheme.{u}} {C : Type v}
    [Category.{w} C] (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M)
    (hf : j.target ≫ f = j.source ≫ f) :
    toQuotientPresheaf F j ≫ quotientToPoints F j f hf =
      F.op.whiskerLeft (yoneda.map f) := by
  simp [quotientToPoints]

/-- If the pre-relation surjects onto the relation cut out by `f`, then the descent of `f` to the
quotient presheaf is locally injective: two points of `U` identified in `M` are locally the two
legs of a point of `R`. -/
private theorem quotientToPoints_isLocallyInjective {S : Scheme.{u}} {C : Type v}
    [Category.{w} C] (J : GrothendieckTopology C) (F : C ⥤ Over S)
    {R U M : Over S} (j : PreRelation R U) (f : U ⟶ M)
    (hf : j.target ≫ f = j.source ≫ f)
    (hR : Presheaf.IsLocallySurjective J
      (F.op.whiskerLeft (yoneda.map (pullback.lift j.target j.source hf)))) :
    Presheaf.IsLocallyInjective J (quotientToPoints F j f hf) := by
  let π := toQuotientPresheaf F j
  let θ := quotientToPoints F j f hf
  let ρ := F.op.whiskerLeft (yoneda.map (pullback.lift j.target j.source hf))
  refine ⟨fun {X} a b hab ↦ ?_⟩
  have hπepi : Epi (π.app X) :=
    (NatTrans.epi_iff_epi_app π).mp (by infer_instance) X
  obtain ⟨x, hx⟩ := (epi_iff_surjective (π.app X)).mp hπepi a
  obtain ⟨y, hy⟩ := (epi_iff_surjective (π.app X)).mp hπepi b
  have hθ (z) : θ.app X (π.app X z) =
      (F.op.whiskerLeft (yoneda.map f)).app X z := by
    simpa [π, θ] using congrArg (fun η => η.app X z)
      (toQuotientPresheaf_quotientToPoints F j f hf)
  have hxy : (F.op.whiskerLeft (yoneda.map f)).app X x =
      (F.op.whiskerLeft (yoneda.map f)).app X y := by
    rw [← hθ, ← hθ, hx, hy]
    exact hab
  have hxy' : x ≫ f = y ≫ f := by simpa using hxy
  let p := pullback.lift x y hxy'
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J ρ p)
  rintro Y g ⟨r, hr⟩
  have hr' : r ≫ pullback.lift j.target j.source hf = F.map g ≫ p := by
    simpa [ρ, points] using hr
  have htarget : r ≫ j.target = F.map g ≫ x := by
    simpa [p, pullback.lift_fst] using congrArg (· ≫ pullback.fst f f) hr'
  have hsource : r ≫ j.source = F.map g ≫ y := by
    simpa [p, pullback.lift_snd] using congrArg (· ≫ pullback.snd f f) hr'
  show (quotientPresheaf F j).map g.op a = (quotientPresheaf F j).map g.op b
  rw [← hx, ← hy, ← NatTrans.naturality_apply π g.op x,
    ← NatTrans.naturality_apply π g.op y]
  calc
    π.app (op Y) ((points F U).map g.op x) =
        π.app (op Y) ((targetMap F j).app (op Y) r) := by
      congr 1
      simpa [targetMap, points] using htarget.symm
    _ = π.app (op Y) ((sourceMap F j).app (op Y) r) := by
      simpa [π] using (congrArg (fun η => η.app (op Y) r)
        (coequalizer.condition (sourceMap F j) (targetMap F j))).symm
    _ = π.app (op Y) ((points F U).map g.op y) :=
      congrArg (π.app (op Y)) (by simpa [sourceMap, points] using hsource)

/-- An invariant map `f : U ⟶ M` which induces a surjection of sheaves on functors of points, and
whose associated relation `U ×_M U` is covered by `R`, exhibits `M` as a representative of the
quotient sheaf `U/R`: the descent of `f` along the canonical projection to the quotient sheaf is an
isomorphism. -/
theorem quotientSheaf_isRepresentedBy_of_locallySurjective
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M)
    (hf : j.target ≫ f = j.source ≫ f)
    (hM : Presheaf.IsSheaf J (points F M))
    (hU : Presheaf.IsLocallySurjective J
      (F.op.whiskerLeft (yoneda.map f)))
    (hR : Presheaf.IsLocallySurjective J
      (F.op.whiskerLeft (yoneda.map (pullback.lift j.target j.source hf)))) :
    ∃ q : quotientSheaf J F j ⟶ (⟨points F M, hM⟩ : Sheaf J (Type u)),
      IsIso q ∧
        toQuotientSheaf J F j ≫ q.hom = F.op.whiskerLeft (yoneda.map f) := by
  let P := quotientPresheaf F j
  let π := toQuotientPresheaf F j
  let θ := quotientToPoints F j f hf
  let ff := F.op.whiskerLeft (yoneda.map f)
  have hdesc : sourceMap F j ≫ ff = targetMap F j ≫ ff := by
    ext X r
    show r ≫ j.source ≫ f = r ≫ j.target ≫ f
    exact congrArg (fun k => r ≫ k) hf.symm
  have : Presheaf.IsLocallySurjective J ff := hU
  have : Presheaf.IsLocallySurjective J θ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (toQuotientPresheaf_quotientToPoints F j f hf)
  have : Presheaf.IsLocallyInjective J θ := quotientToPoints_isLocallyInjective J F j f hf hR
  let η := toSheafify J P
  let A : Sheaf J (Type u) := ⟨points F M, hM⟩
  let Q := quotientSheaf J F j
  let q : Q ⟶ A := quotientSheafDesc J F j A ff hdesc
  have hq : toQuotientSheaf J F j ≫ q.hom = ff :=
    toQuotientSheaf_quotientSheafDesc J F j A ff hdesc
  have hηq : η ≫ q.hom = θ :=
    (cancel_epi π).1 (hq.trans (toQuotientPresheaf_quotientToPoints F j f hf).symm)
  obtain ⟨g, hg, _⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J θ η Q.property
  let inv : A ⟶ Q := ⟨g⟩
  have hqgFac : toQuotientSheaf J F j ≫ (q ≫ inv).hom = toQuotientSheaf J F j := by
    show (toQuotientSheaf J F j ≫ q.hom) ≫ g = π ≫ η
    rw [hq, ← hg, ← Category.assoc]
    exact congrArg (· ≫ g) (toQuotientPresheaf_quotientToPoints F j f hf).symm
  have hqg : q.hom ≫ g = 𝟙 Q.obj := by
    simpa [inv] using congrArg (fun t : Q ⟶ Q => t.hom)
      ((quotientSheafDesc_unique J F j Q (toQuotientSheaf J F j)
        (sourceMap_toQuotientSheaf J F j) (q ≫ inv) hqgFac).trans
      (quotientSheafDesc_unique J F j Q (toQuotientSheaf J F j)
        (sourceMap_toQuotientSheaf J F j) (𝟙 Q) (Category.comp_id _)).symm)
  obtain ⟨k, -, hkunique⟩ :=
    Presheaf.existsUnique_hom_of_isLocallyBijective J θ θ hM
  have hkg : g ≫ q.hom = 𝟙 A.obj :=
    (hkunique _ (by beta_reduce; rw [← Category.assoc, hg, hηq])).trans
      (hkunique _ (Category.comp_id θ)).symm
  let e : Q ≅ A :=
    { hom := q
      inv := inv
      hom_inv_id := Sheaf.hom_ext hqg
      inv_hom_id := Sheaf.hom_ext hkg }
  exact ⟨q, e.isIso_hom, hq⟩

end Stacks.Groupoids

end
