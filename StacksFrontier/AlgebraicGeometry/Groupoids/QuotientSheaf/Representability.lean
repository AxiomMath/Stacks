module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# A criterion for a quotient sheaf to be represented

Let `j : R ⟶ U ×_S U` be a pre-relation over `S` and let `f : U ⟶ M` be a morphism of
`S`-schemes equalizing the source and the target of `j`. Then `f` descends to a canonical map
`U/R ⟶ h_M` of sheaves, and that map is an isomorphism — so `M` represents the quotient sheaf
— as soon as `f` induces a surjection of sheaves and `(t, s) : R ⟶ U ×_M U` induces a
surjection of sheaves.

## Main definitions

* `Stacks.Groupoids.quotientPresheafToPoints` is the descent of `h_f` to the quotient
  presheaf, and `Stacks.Groupoids.quotientSheafToPoints` is its descent to the quotient sheaf.

## Main results

* `Stacks.Groupoids.isIso_quotientSheafToPoints` says that `M` represents `U/R` under the two
  surjectivity hypotheses.
* `Stacks.Groupoids.quotientPresheafToPoints_isLocallyInjective`: the descent to the quotient
  presheaf is locally injective when `(t, s) : R ⟶ U ×_M U` induces a surjection of sheaves.
* `Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafToPoints` and
  `Stacks.Groupoids.toQuotientPresheaf_comp_quotientPresheafToPoints` identify the composites
  of the canonical projections with these maps as `h_f`.

## References

* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- A morphism `f : U ⟶ M` equalizing the source and the target of a pre-relation induces a
map of functors of points which coequalizes the two maps of that pre-relation. -/
theorem sourceMap_comp_yonedaMap (F : C ⥤ Over S) {R U M : Over S} (j : PreRelation R U)
    (f : U ⟶ M) (hf : j.target ≫ f = j.source ≫ f) :
    sourceMap F j ≫ F.op.whiskerLeft (yoneda.map f) =
      targetMap F j ≫ F.op.whiskerLeft (yoneda.map f) := by
  ext X r
  change r ≫ j.source ≫ f = r ≫ j.target ≫ f
  exact congrArg (fun k => r ≫ k) hf.symm

/-- The descent to the quotient presheaf of the map of functors of points of a morphism
`f : U ⟶ M` equalizing the source and the target of a pre-relation. -/
noncomputable def quotientPresheafToPoints (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M) (hf : j.target ≫ f = j.source ≫ f) :
    quotientPresheaf F j ⟶ points F M :=
  coequalizer.desc (F.op.whiskerLeft (yoneda.map f)) (sourceMap_comp_yonedaMap F j f hf)

/-- The descent to the quotient presheaf agrees with the map of functors of points of `f`. -/
theorem toQuotientPresheaf_comp_quotientPresheafToPoints (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M) (hf : j.target ≫ f = j.source ≫ f) :
    toQuotientPresheaf F j ≫ quotientPresheafToPoints F j f hf =
      F.op.whiskerLeft (yoneda.map f) := by
  simp [quotientPresheafToPoints]

/-- If `R` covers `U ×_M U` locally, then the descent of `h_f` to the quotient presheaf is
locally injective. -/
theorem quotientPresheafToPoints_isLocallyInjective (J : GrothendieckTopology C)
    (F : C ⥤ Over S) {R U M : Over S} (j : PreRelation R U) (f : U ⟶ M)
    (hf : j.target ≫ f = j.source ≫ f)
    (hR : Presheaf.IsLocallySurjective J
      (F.op.whiskerLeft (yoneda.map (pullback.lift j.target j.source hf)))) :
    Presheaf.IsLocallyInjective J (quotientPresheafToPoints F j f hf) := by
  let π := toQuotientPresheaf F j
  let θ := quotientPresheafToPoints F j f hf
  let ρ := F.op.whiskerLeft (yoneda.map (pullback.lift j.target j.source hf))
  refine ⟨fun {X} a b hab ↦ ?_⟩
  have hπ : Function.Surjective (π.app X) :=
    (epi_iff_surjective _).mp ((NatTrans.epi_iff_epi_app π).mp inferInstance X)
  obtain ⟨x, hx⟩ := hπ a
  obtain ⟨y, hy⟩ := hπ b
  have hθ (z) : θ.app X (π.app X z) = (F.op.whiskerLeft (yoneda.map f)).app X z := by
    simpa [π, θ] using congrArg (fun η => η.app X z)
      (toQuotientPresheaf_comp_quotientPresheafToPoints F j f hf)
  have hxy : (F.op.whiskerLeft (yoneda.map f)).app X x =
      (F.op.whiskerLeft (yoneda.map f)).app X y := by
    rw [← hθ x, ← hθ y, hx, hy]
    exact hab
  have hxy' : x ≫ f = y ≫ f := by simpa using hxy
  apply J.superset_covering ?_
    (Presheaf.imageSieve_mem J ρ (pullback.lift x y hxy'))
  rintro Y g ⟨r, hr⟩
  have hr' : r ≫ pullback.lift j.target j.source hf =
      F.map g ≫ pullback.lift x y hxy' := by simpa [ρ, points] using hr
  have htarget : r ≫ j.target = F.map g ≫ x := by
    simpa [Category.assoc, pullback.lift_fst] using
      congrArg (fun k => k ≫ pullback.fst f f) hr'
  have hsource : r ≫ j.source = F.map g ≫ y := by
    simpa [Category.assoc, pullback.lift_snd] using
      congrArg (fun k => k ≫ pullback.snd f f) hr'
  have hrel : π.app (op Y) ((targetMap F j).app (op Y) r) =
      π.app (op Y) ((sourceMap F j).app (op Y) r) := by
    simpa [π] using (congrArg (fun η => η.app (op Y) r)
      (coequalizer.condition (sourceMap F j) (targetMap F j))).symm
  change (quotientPresheaf F j).map g.op a = (quotientPresheaf F j).map g.op b
  rw [← hx, ← hy, ← NatTrans.naturality_apply π g.op x, ← NatTrans.naturality_apply π g.op y]
  calc
    π.app (op Y) ((points F U).map g.op x) =
        π.app (op Y) ((targetMap F j).app (op Y) r) := by
      congr 1
      simpa [targetMap, points] using htarget.symm
    _ = π.app (op Y) ((sourceMap F j).app (op Y) r) := hrel
    _ = π.app (op Y) ((points F U).map g.op y) :=
      congrArg (fun z => π.app (op Y) z) (by simpa [sourceMap, points] using hsource)

variable (J : GrothendieckTopology C) [HasSheafify J (Type u)]

/-- The descent to the quotient sheaf of the map of functors of points of a morphism
`f : U ⟶ M` equalizing the source and the target of a pre-relation, as a map into the sheaf of
points of `M`. -/
noncomputable def quotientSheafToPoints (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M) (hf : j.target ≫ f = j.source ≫ f)
    (hM : Presheaf.IsSheaf J (points F M)) :
    quotientSheaf J F j ⟶ (⟨points F M, hM⟩ : Sheaf J (Type u)) :=
  quotientSheafDesc J F j ⟨points F M, hM⟩ (F.op.whiskerLeft (yoneda.map f))
    (sourceMap_comp_yonedaMap F j f hf)

/-- The descent to the quotient sheaf agrees with the map of functors of points of `f`. -/
theorem toQuotientSheaf_comp_quotientSheafToPoints (F : C ⥤ Over S) {R U M : Over S}
    (j : PreRelation R U) (f : U ⟶ M) (hf : j.target ≫ f = j.source ≫ f)
    (hM : Presheaf.IsSheaf J (points F M)) :
    toQuotientSheaf J F j ≫ (quotientSheafToPoints J F j f hf hM).hom =
      F.op.whiskerLeft (yoneda.map f) :=
  toQuotientSheaf_quotientSheafDesc J F j ⟨points F M, hM⟩ (F.op.whiskerLeft (yoneda.map f))
    (sourceMap_comp_yonedaMap F j f hf)

/-- Let `f : U ⟶ M` equalize the source and the target of a pre-relation
`j : R ⟶ U ×_S U`, let the functor of points of `M` be a sheaf, let `f` induce a locally
surjective map of functors of points, and let `(t, s) : R ⟶ U ×_M U` induce a locally
surjective map of functors of points. Then `M` represents the quotient sheaf `U/R`: the
canonical map `U/R ⟶ h_M` is an isomorphism. -/
theorem isIso_quotientSheafToPoints (F : C ⥤ Over S) {R U M : Over S} (j : PreRelation R U)
    (f : U ⟶ M) (hf : j.target ≫ f = j.source ≫ f)
    (hM : Presheaf.IsSheaf J (points F M))
    (hU : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map f)))
    (hR : Presheaf.IsLocallySurjective J
      (F.op.whiskerLeft (yoneda.map (pullback.lift j.target j.source hf)))) :
    IsIso (quotientSheafToPoints J F j f hf hM) := by
  let π := toQuotientPresheaf F j
  let θ := quotientPresheafToPoints F j f hf
  let ff := F.op.whiskerLeft (yoneda.map f)
  let A : Sheaf J (Type u) := ⟨points F M, hM⟩
  let Q := quotientSheaf J F j
  let η := toSheafify J (quotientPresheaf F j)
  let q : Q ⟶ A := quotientSheafToPoints J F j f hf hM
  let _ : Presheaf.IsLocallySurjective J ff := hU
  have hπθ : π ≫ θ = ff := toQuotientPresheaf_comp_quotientPresheafToPoints F j f hf
  let _ : Presheaf.IsLocallySurjective J θ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hπθ
  let _ : Presheaf.IsLocallyInjective J θ :=
    quotientPresheafToPoints_isLocallyInjective J F j f hf hR
  have hq : toQuotientSheaf J F j ≫ q.hom = ff :=
    toQuotientSheaf_comp_quotientSheafToPoints J F j f hf hM
  have hηq : η ≫ q.hom = θ := by
    apply (cancel_epi π).1
    exact hq.trans hπθ.symm
  obtain ⟨g, hg, -⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J θ η Q.property
  have hqgFac : toQuotientSheaf J F j ≫ (q ≫ (⟨g⟩ : A ⟶ Q)).hom = toQuotientSheaf J F j := by
    change toQuotientSheaf J F j ≫ q.hom ≫ g = π ≫ η
    rw [← Category.assoc, hq, ← hg, ← Category.assoc]
    exact congrArg (· ≫ g) hπθ.symm
  have hqg : q.hom ≫ g = 𝟙 Q.obj := by
    have hd := quotientSheafDesc_unique J F j Q (toQuotientSheaf J F j)
      (sourceMap_toQuotientSheaf J F j)
    exact congrArg (fun t : Q ⟶ Q => t.hom)
      ((hd _ hqgFac).trans (hd (𝟙 Q) (Category.comp_id _)).symm)
  obtain ⟨k, -, hkunique⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J θ θ hM
  have hkg : g ≫ q.hom = 𝟙 A.obj :=
    (hkunique (g ≫ q.hom) (by change θ ≫ g ≫ q.hom = θ; rw [← Category.assoc, hg, hηq])).trans
      (hkunique (𝟙 A.obj) (Category.comp_id θ)).symm
  exact (Iso.mk q (⟨g⟩ : A ⟶ Q) (Sheaf.hom_ext hqg) (Sheaf.hom_ext hkg)).isIso_hom

end Stacks.Groupoids

end
