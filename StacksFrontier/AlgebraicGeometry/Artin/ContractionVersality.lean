module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionVersality
public import StacksFrontier.Deformation.Artin.FunctorOpenVersality
import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionComparison
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction

/-!
# Versality of an element of Artin's contraction functor at a point of `Z`

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA and let
`ξ = (Z, u', x̂) ∈ F(V)`. A lifting problem for versality of `ξ` at a point `v ∈ V` (Stacks 07XF)
lives over spectra of Artinian local rings with closed point going to `v`. On such a one-point
scheme a triple is a point of `U'` or a point of `W` (Stacks 0GI6, 0GI7), and which of the two
it is depends only on whether `v ∈ Z`. This file shows that for `v ∈ Z` versality of `ξ` at `v`
is versality of `x̂ : V_{/Z} ⟶ W` at `v` in the sense of Stacks 0GI9,
`AlgebraicGeometry.FormalSpace.IsVersalAtCompletion`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isVersalAt_iff_isVersalAtCompletion`: for
  `v ∈ Z`, `ξ` is versal at `v` exactly when `x̂` is.

## References

* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The point space of the presheaf represented by an object of the site whose underlying scheme
is a single point `t` is a single point, and a morphism `φ : T ⟶ V` sends it to the point of
`|V|` corresponding to the image of `t`. -/
theorem range_pointsMap_yoneda_map_of_subsingleton {T V : BigFppfOver B S hS}
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (φ : T ⟶ V)
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    Set.range (pointsMap B S hS (yoneda.obj T) (yoneda.map φ)) =
      {(pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map φ t)} := by
  have key (w' : Space.points B S hS (yoneda.obj T)) :
      pointsMap B S hS (yoneda.obj T) (yoneda.map φ) w' =
        (pointsEquivScheme B S hS V).symm
          ((BigFppfOver.toScheme B S hS).map φ (pointsEquivScheme B S hS T w')) := by
    apply (pointsEquivScheme B S hS V).injective
    rw [Equiv.apply_symm_apply]
    change pointsToScheme B S hS V _ = _
    rw [pointsToScheme_pointsMap_yoneda]
    rfl
  ext w
  constructor
  · rintro ⟨w', rfl⟩
    rw [key, Subsingleton.elim (pointsEquivScheme B S hS T w') t]
    rfl
  · rintro rfl
    exact ⟨(pointsEquivScheme B S hS T).symm t, by rw [key, Equiv.apply_symm_apply]⟩

/-- The element of `yoneda.obj V` corresponding to `φ` under `yonedaEquiv` is `yoneda.map φ`. -/
private theorem yonedaEquiv_symm_eq_yoneda_map {T V : BigFppfOver B S hS} (φ : T ⟶ V) :
    yonedaEquiv.symm φ = yoneda.map φ := by
  ext; rfl

/-- A morphism out of a one-point object of the site has point-set image in `Z` exactly when the
image of the point lies in `Z`. -/
theorem hasImageIn_iff_of_subsingleton {T V : BigFppfOver B S hS}
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (φ : T ⟶ V)
    (t : (BigFppfOver.toScheme B S hS).obj T) (Z : Set (points B S hS (yoneda.obj V))) :
    HasImageIn B S hS (yoneda.obj V) Z T φ ↔
      (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map φ t) ∈ Z := by
  rw [hasImageIn_iff_range_subset B S hS, yonedaEquiv_symm_eq_yoneda_map,
    range_pointsMap_yoneda_map_of_subsingleton φ t, Set.singleton_subset_iff]

/-- A morphism out of a one-point object of the site is a section of the open subspace cut out
by `W` exactly when the image of the point lies in `W`. -/
theorem mem_openSubspaceOfPoints_iff_of_subsingleton {T V : BigFppfOver B S hS}
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (φ : T ⟶ V)
    (t : (BigFppfOver.toScheme B S hS).obj T) (W : Set (points B S hS (yoneda.obj V))) :
    φ ∈ (openSubspaceOfPoints B S hS (yoneda.obj V) W).obj (op T) ↔
      (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map φ t) ∈ W := by
  rw [mem_openSubspaceOfPoints_iff B S hS, yonedaEquiv_symm_eq_yoneda_map,
    range_pointsMap_yoneda_map_of_subsingleton φ t, Set.singleton_subset_iff]

end Space

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-! ### The components of a transported triple -/

/-- Transporting a triple along `φ : T ⟶ V` whose point-set image lies in `Z`, the section of
`W` of the transported triple (whose closed subset is then everything) is `x̂` applied to the
section of `V_{/Z}` given by `φ`. -/
theorem wSection_mapTriple_eq {T V : BigFppfOver B S hS} (φ : T ⟶ V) (t : Triple c V)
    (hφ : Space.HasImageIn B S hS (yoneda.obj V) t.Z T φ)
    (h : (mapTriple c φ t).Z = Set.univ) :
    wSection c (mapTriple c φ t) h =
      t.xhat.hom.app (op T) (FormalSpace.presheafSection B S hS (T := t.Z) φ hφ) := by
  have hleft : (yoneda.map φ).app (op T) (𝟙 T) = φ := by simp
  change t.xhat.hom.app (op T)
      ((Space.completionSheafRestrict B S hS (yoneda.map φ) (mapTriple c φ t).Z t.Z
        (mapTriple_Z_eq_preimage c φ t).subset).hom.app (op T)
          (FormalSpace.completionIdSection B S hS T (mapTriple c φ t).Z h)) = _
  rw [FormalSpace.completionIdSection,
    FormalSpace.completionSheafRestrict_presheafSection B S hS (yoneda.map φ) _ t.Z _ (𝟙 T) _
      (by rw [hleft]; exact hφ),
    FormalSpace.presheafSection_congr B S hS hleft _ hφ]

/-- Transporting a triple along `φ : T ⟶ V` whose point-set image avoids `Z`, the point of `U'`
of the transported triple (whose closed subset is then empty) is `u'` applied to the section of
`V ∖ Z` given by `φ`. -/
theorem uPoint_mapTriple_eq {T V : BigFppfOver B S hS} (φ : T ⟶ V) (t : Triple c V)
    (hφ : φ ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T))
    (h : (mapTriple c φ t).Z = ∅) :
    (mapTriple c φ t).uPoint h = t.u.app (op T) ⟨φ, hφ⟩ := by
  change t.u.app (op T) ((Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) _ t.Zᶜ
      (fun _ hz => hz)).app (op T) ⟨𝟙 T, _⟩) = _
  congr 1

/-! ### Test objects -/

section TestObjects

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A] [IsArtinianRing A]
  [IsLocalRing A] {iΛ : Spec (.of Λ) ⟶ S} {T : BigFppfOver B S hS}

omit [IsLocalRing A] in
/-- An object of the site lying over the spectrum of an Artinian ring is locally Noetherian. -/
theorem isLocallyNoetherian_of_over_spec
    (hT : (Over.post B.inclusion).obj T = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap Λ A)) ≫ iΛ)) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) := by
  have e : (BigFppfOver.toScheme B S hS).obj T = Spec (.of A) := congrArg Over.left hT
  rw [e]
  infer_instance

/-- An object of the site lying over the spectrum of an Artinian local ring has one point. -/
theorem subsingleton_of_over_spec
    (hT : (Over.post B.inclusion).obj T = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap Λ A)) ≫ iΛ)) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj T) := by
  have e : (BigFppfOver.toScheme B S hS).obj T = Spec (.of A) := congrArg Over.left hT
  rw [e]
  exact ⟨Deformation.Artin.subsingleton_spec_of_isArtinianRing A⟩

end TestObjects

/-- If a morphism `ρ` out of the spectrum of the residue field of `v` followed by `φ : T ⟶ V` is
the residue point of `v`, then `φ` sends some point of `T` to `v`. -/
theorem exists_map_eq_of_residue {T V : BigFppfOver B S hS} {X : Scheme.{u}}
    (v : (BigFppfOver.toScheme B S hS).obj V) (e : X = (BigFppfOver.toScheme B S hS).obj T)
    (ρ : Spec (((BigFppfOver.toScheme B S hS).obj V).residueField v) ⟶ X) (φ : T ⟶ V)
    (h : ρ ≫ eqToHom e ≫ ((Over.post B.inclusion).map φ).left =
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v) :
    ∃ t, (BigFppfOver.toScheme B S hS).map φ t = v := by
  let s : Spec (((BigFppfOver.toScheme B S hS).obj V).residueField v) :=
    IsLocalRing.closedPoint _
  have hs : ((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v s = v :=
    Scheme.fromSpecResidueField_apply _ _
  have h2 : (ρ ≫ eqToHom e ≫ ((Over.post B.inclusion).map φ).left) s = v := by
    rw [h]; exact hs
  exact ⟨(ρ ≫ eqToHom e) s, h2⟩

/-- A morphism `φ : T ⟶ V` has point-set image in the closed subset of a triple exactly when the
transported triple has closed subset everything. -/
theorem mapTriple_Z_eq_univ_iff {T V : BigFppfOver B S hS} (φ : T ⟶ V) (t : Triple c V) :
    (mapTriple c φ t).Z = Set.univ ↔ Space.HasImageIn B S hS (yoneda.obj V) t.Z T φ := by
  rw [Space.hasImageIn_iff_range_subset B S hS, Space.yonedaEquiv_symm_eq_yoneda_map,
    mapTriple_Z_eq_preimage, Set.preimage_eq_univ_iff]

/-! ### Versality at a point of `Z` -/

/-- **Versality at a point of `Z`.** For `ξ = (Z, u', x̂) ∈ F(V)` and a point `v` of `V` lying in
`Z`, `ξ` is versal at `v` (Stacks 07XF) exactly when `x̂ : V_{/Z} ⟶ W` is versal at `v` in the
sense of Stacks 0GI9: a lifting problem for `ξ` is one for `x̂`, because a triple on the spectrum
of an Artinian local ring whose closed point goes to `Z` is a point of `W`. -/
theorem isVersalAt_iff_isVersalAtCompletion (x : (contractionFunctor c).Elementsᵒᵖ)
    (v : (BigFppfOver.toScheme B S hS).obj x.unop.obj.unop.obj)
    (hv : (Space.pointsEquivScheme B S hS x.unop.obj.unop.obj).symm v ∈
      (x.unop.val : Triple c x.unop.obj.unop.obj).Z) :
    Deformation.Artin.IsVersalAt
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) v x rfl ↔
      FormalSpace.IsVersalAtCompletion B S hS x.unop.obj.unop.obj
        (x.unop.val : Triple c x.unop.obj.unop.obj).Z c.W
        (x.unop.val : Triple c x.unop.obj.unop.obj).xhat v := by
  let ξ : Triple c x.unop.obj.unop.obj := x.unop.val
  constructor
  · intro hver A A' f hf T T' hT hT' i hi φ hφ hres w' hw'
    have := subsingleton_of_over_spec hT
    have := subsingleton_of_over_spec hT'
    let TN : LocallyNoetherianOver B S hS := ⟨T, isLocallyNoetherian_of_over_spec hT⟩
    let T'N : LocallyNoetherianOver B S hS := ⟨T', isLocallyNoetherian_of_over_spec hT'⟩
    let z : (contractionFunctor c).Elementsᵒᵖ :=
      op (Functor.elementsMk _ (op T'N) (c.tripleOfSection T' w'))
    let y : (contractionFunctor c).Elementsᵒᵖ :=
      op (Functor.elementsMk _ (op TN) (mapTriple c φ ξ))
    have hyZ : (mapTriple c φ ξ).Z = Set.univ := (mapTriple_Z_eq_univ_iff c φ ξ).2 hφ
    have hi' : mapTriple c i (c.tripleOfSection T' w') = mapTriple c φ ξ := by
      refine Triple.eq_of_Z_eq_univ c _ _ (Triple.mapTriple_Z_eq_univ c i _ rfl) hyZ ?_
      rw [wSection_mapTriple c i _ rfl, wSection_tripleOfSection, hw',
        wSection_mapTriple_eq c φ ξ hφ hyZ]
    let iE : y ⟶ z := Quiver.Hom.op ⟨(ObjectProperty.homMk i : TN ⟶ T'N).op, hi'⟩
    let aE : y ⟶ x := Quiver.Hom.op ⟨(ObjectProperty.homMk φ : TN ⟶ x.unop.obj.unop).op, rfl⟩
    obtain ⟨b, hb⟩ := hver A A' f hf y z hT hT' iE hi aE (by
      simp only [eqToHom_refl, Category.comp_id]
      exact hres)
    have hb' : mapTriple c b.unop.hom.unop.hom ξ = c.tripleOfSection T' w' := b.unop.map_val
    have hZ' : (mapTriple c b.unop.hom.unop.hom ξ).Z = Set.univ := by rw [hb']; rfl
    have hφ' := (mapTriple_Z_eq_univ_iff c _ ξ).1 hZ'
    refine ⟨b.unop.hom.unop.hom, hφ', ?_, ?_⟩
    · exact congrArg (fun m : y ⟶ x => m.unop.hom.unop.hom) hb
    · rw [← wSection_mapTriple_eq c _ ξ hφ' hZ', wSection_congr c hb' hZ' rfl,
        wSection_tripleOfSection]
  · intro hlift A A' f hf y z hy hz i hi a ha
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj y.unop.obj.unop.obj) :=
      subsingleton_of_over_spec hy
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj z.unop.obj.unop.obj) :=
      subsingleton_of_over_spec hz
    have ha' := ha
    simp only [eqToHom_refl, Category.comp_id] at ha'
    obtain ⟨t, ht⟩ := exists_map_eq_of_residue (T := y.unop.obj.unop.obj)
      (V := x.unop.obj.unop.obj) v (congrArg Over.left hy).symm _ a.unop.hom.unop.hom ha'
    have hφ : Space.HasImageIn B S hS (yoneda.obj x.unop.obj.unop.obj) ξ.Z y.unop.obj.unop.obj
        a.unop.hom.unop.hom :=
      (Space.hasImageIn_iff_of_subsingleton (T := y.unop.obj.unop.obj) _ t _).2
        (by rw [ht]; exact hv)
    have hya : mapTriple c a.unop.hom.unop.hom ξ = y.unop.val := a.unop.map_val
    have hzi : mapTriple c i.unop.hom.unop.hom z.unop.val = y.unop.val := i.unop.map_val
    have hZa := (mapTriple_Z_eq_univ_iff c a.unop.hom.unop.hom ξ).2 hφ
    have hyZ : (y.unop.val : Triple c y.unop.obj.unop.obj).Z = Set.univ := by
      rw [← hya]; exact hZa
    have hzZ : (z.unop.val : Triple c z.unop.obj.unop.obj).Z = Set.univ := by
      rcases Triple.Z_eq_empty_or_eq_univ (z.unop.val : Triple c z.unop.obj.unop.obj) with h | h
      · exfalso
        have h0 := Triple.mapTriple_Z_eq_empty c i.unop.hom.unop.hom _ h
        rw [hzi, hyZ] at h0
        exact (Set.mem_empty_iff_false ((Space.pointsEquivScheme B S hS _).symm t)).1
          (h0 ▸ Set.mem_univ _)
      · exact h
    have hw' : c.W.obj.map i.unop.hom.unop.hom.op (wSection c z.unop.val hzZ) =
        ξ.xhat.hom.app (op y.unop.obj.unop.obj)
          (FormalSpace.presheafSection B S hS (T := ξ.Z) a.unop.hom.unop.hom hφ) := by
      rw [← wSection_mapTriple c _ _ hzZ (Triple.mapTriple_Z_eq_univ c _ _ hzZ),
        wSection_congr c hzi _ hyZ,
        ← wSection_congr c hya hZa hyZ,
        wSection_mapTriple_eq c _ ξ hφ]
    obtain ⟨φ', hφ', hcomp, hval⟩ :=
      hlift A A' f hf _ _ hy hz i.unop.hom.unop.hom hi _ hφ ha' _ hw'
    have hZ' := (mapTriple_Z_eq_univ_iff c φ' ξ).2 hφ'
    have hb : mapTriple c φ' ξ = z.unop.val :=
      Triple.eq_of_Z_eq_univ c _ _ hZ' hzZ
        (by rw [wSection_mapTriple_eq c φ' ξ hφ' hZ']; exact hval)
    refine ⟨Quiver.Hom.op ⟨(ObjectProperty.homMk φ' : z.unop.obj.unop ⟶ x.unop.obj.unop).op, hb⟩,
      ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact hcomp

end Artin.ContractionSituation

end AlgebraicGeometry

end
