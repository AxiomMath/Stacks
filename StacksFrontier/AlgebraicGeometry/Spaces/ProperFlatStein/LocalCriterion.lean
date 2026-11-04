module

public import StacksFrontier.AlgebraicGeometry.Descent.FiniteEtaleCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# A pointwise étale-local criterion for a finite étale morphism of algebraic spaces

This is a helper module of the proof of Stacks 0E0D. Its declarations are scoped to the
`AlgebraicGeometry.Space.ProperFlatStein` namespace and it records no tag.

Let `Y` be an algebraic space over `S` and let `π : Y' ⟶ Y` be an affine morphism of presheaves
on the big fppf site of `S`. Suppose that every point `y` of `Y` lies in the image of an étale
morphism `ξ : h_U ⟶ Y` from a representable presheaf over which `π` becomes a finite étale
morphism of schemes `V ⟶ U`. Then `π` is finite and étale.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.presheaf_pullback_snd_of_forall_point`: a property of
  morphisms of schemes which is Zariski local on the target and satisfies fppf descent holds for a
  represented base change of a morphism of presheaves `f` along any `ζ : h_W ⟶ Y`, as soon as it
  holds for the base changes along the composites `h_b ⟶ h_{U_i} ⟶ Y` for a family of étale
  morphisms `ξ_i : h_{U_i} ⟶ Y` which is jointly surjective on points.
* `AlgebraicGeometry.Space.ProperFlatStein.isFinite_and_isEtale_of_forall_point`: the local
  criterion.

## Implementation notes

The base changes of the given étale neighbourhoods along `ζ` are étale over `W` and, by
Stacks 03H4 (`AlgebraicGeometry.Space.exists_points_of_isPullback`) together with the comparison
of the points of a represented presheaf with those of its scheme (Stacks 03BV), jointly
surjective onto the scheme of `W`. They therefore generate a covering sieve, along which the
property descends by `AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`.

Finiteness is tested only over affine objects of the site, where the affineness of `π` supplies
both the representability of the base change and the affineness of its representing object.
Étaleness needs every base change of a composite `h_U ⟶ Y' ⟶ Y`; that one is representable
because its source is representable and `Y` has representable diagonal, and étale by the same
descent applied with the property of being étale. No algebraicity of `Y'` is needed.

## References

* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Represented base changes and the chosen pullback -/

/-- The chosen base change of a morphism of presheaves along a morphism from a representable
presheaf is relatively representable as soon as some represented base change exists. -/
theorem relativelyRepresentable_pullback_snd_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {a b : BigFppfOver B S hS}
    {g : yoneda.obj a ⟶ Y} {fst : yoneda.obj b ⟶ X} {s : b ⟶ a}
    (sq : IsPullback fst (yoneda.map s) f g) :
    yoneda.relativelyRepresentable (pullback.snd f g) := by
  have h := Functor.relativelyRepresentable.map yoneda s
  rw [← sq.isoPullback_hom_snd] at h
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 h

/-- The relatively representable form of a property for the chosen base change gives the
property for every represented base change; the converse is
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback`. -/
theorem of_presheaf_pullback_snd_of_isPullback {Q : MorphismProperty Scheme.{u}}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {a b : BigFppfOver B S hS}
    {g : yoneda.obj a ⟶ Y} {fst : yoneda.obj b ⟶ X} {s : b ⟶ a}
    (sq : IsPullback fst (yoneda.map s) f g)
    (h : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    Q ((BigFppfOver.toScheme B S hS).map s) := by
  have h' := (MorphismProperty.cancel_left_of_respectsIso _ sq.isoPullback.hom _).2 h
  rw [sq.isoPullback_hom_snd] at h'
  exact MorphismProperty.of_relative_map (F := yoneda)
    (P := Q.inverseImage (BigFppfOver.toScheme B S hS)) h'

/-! ### Descent along a pointwise family of étale neighbourhoods -/

/-- **Descent along a family of étale neighbourhoods which is jointly surjective on points.**
Let `ξ_i : h_{U_i} ⟶ Y` be étale morphisms from representable presheaves whose images cover the
points of `Y`, and let `Q` be a property of morphisms of schemes which is Zariski local on the
target and descends along the surjective flat morphisms locally of finite presentation. If the
base change of `f : X ⟶ Y` along every composite `h_b ⟶ h_{U_i} ⟶ Y` is representable with `Q`,
then so is its base change along any `ζ : h_W ⟶ Y` for which it is representable at all. -/
theorem presheaf_pullback_snd_of_forall_point {Q : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget Q]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type (u + 1)} {U : I → BigFppfOver B S hS}
    (ξ : ∀ i, yoneda.obj (U i) ⟶ Y)
    (hξ : ∀ i, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (ξ i))
    (hcov : ∀ y : points B S hS Y, ∃ i, y ∈ Set.range (pointsMap B S hS (yoneda.obj (U i)) (ξ i)))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hloc : ∀ (i : I) {b : BigFppfOver B S hS} (r : b ⟶ U i),
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map r ≫ ξ i)))
    {W : BigFppfOver B S hS} (ζ : yoneda.obj W ⟶ Y)
    (hrep : yoneda.relativelyRepresentable (pullback.snd f ζ)) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f ζ) := by
  have hsieve : Sieve.ofArrows (fun i ↦ (hξ i).rep.pullback ζ) (fun i ↦ (hξ i).rep.snd ζ) ∈
      BigFppfOver.topology B S hS W := by
    refine BigFppfOver.ofArrows_mem_topology_of_etale B S hS _ _
      (fun i ↦ (hξ i).property_snd ζ) fun x ↦ ?_
    obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS W x
    obtain ⟨i, v, hv⟩ := hcov (pointsMap B S hS (yoneda.obj W) ζ w)
    obtain ⟨z, -, hz⟩ := exists_points_of_isPullback B S hS ((hξ i).rep.isPullback ζ) v w hv
    exact ⟨i, pointsToScheme B S hS _ z, by
      rw [← pointsToScheme_pointsMap_yoneda, hz]⟩
  refine presheaf_of_coveringSieve_of_descendsAlong ζ hrep hsieve fun b q hq ↦ ?_
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ q).1 hq
  have heq : yoneda.map (c ≫ (hξ i).rep.snd ζ) ≫ ζ =
      yoneda.map (c ≫ (hξ i).rep.fst' ζ) ≫ ξ i := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      Functor.relativelyRepresentable.map_fst', ← (hξ i).rep.w ζ]
  have hcongr : ∀ {g g' : yoneda.obj b ⟶ Y}, g = g' →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g') := by
    rintro g g' rfl hg
    exact hg
  exact hcongr heq.symm (hloc i _)

/-! ### The local criterion -/

/-- **A pointwise étale-local criterion for a finite étale morphism.** Let `Y` be an algebraic
space over `S` and `π : Y' ⟶ Y` an affine morphism. If every point of `Y` lies in the image of an
étale morphism `ξ : h_U ⟶ Y` over which `π` is represented by a finite étale morphism of schemes
`V ⟶ U`, then `π` is finite and étale. -/
theorem isFinite_and_isEtale_of_forall_point
    {Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (π : Y' ⟶ Y) (hπ : IsAffineHom B S hS π)
    (h : ∀ y : points B S hS Y, ∃ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ Y)
        (V : BigFppfOver B S hS) (p : V ⟶ U) (i : yoneda.obj V ⟶ Y'),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ξ ∧
        y ∈ Set.range (pointsMap B S hS (yoneda.obj U) ξ) ∧
        IsPullback i (yoneda.map p) π ξ ∧
        _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) ∧
        AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p)) :
    IsFinite B S hS π ∧ IsEtale B S hS π := by
  choose U ξ V p i hξ hy hsq hfin het using h
  have hcov : ∀ y : points B S hS Y, ∃ y', y ∈ Set.range (pointsMap B S hS _ (ξ y')) :=
    fun y ↦ ⟨y, hy y⟩
  -- The base change of `π` along `h_b ⟶ h_{U_y} ⟶ Y` is represented by `V_y ×_{U_y} b`.
  have sq : ∀ (y : points B S hS Y) {b : BigFppfOver B S hS} (r : b ⟶ U y),
      IsPullback (yoneda.map (pullback.fst (p y) r) ≫ i y)
        (yoneda.map (pullback.snd (p y) r)) π (yoneda.map r ≫ ξ y) :=
    fun y _ r ↦ ((IsPullback.of_hasPullback (p y) r).map yoneda).paste_horiz (hsq y)
  have hbc : ∀ (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
      (y : points B S hS Y) {b : BigFppfOver B S hS} (r : b ⟶ U y),
      Q ((BigFppfOver.toScheme B S hS).map (p y)) →
        Q ((BigFppfOver.toScheme B S hS).map (pullback.snd (p y) r)) := by
    intro Q _ y b r hQ
    have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS Q
    exact MorphismProperty.pullback_snd (P := Q.inverseImage (BigFppfOver.toScheme B S hS))
      (p y) r hQ
  refine ⟨fun W hW ζ ↦ ?_, fun U₀ φ hφ ↦ ?_⟩
  · -- Finiteness, tested over an affine object of the site.
    have := isFinite_inf_etale_isZariskiLocalAtTarget.{u}
    have := isFinite_inf_etale_descendsAlong_fppf.{u}
    have : (@_root_.AlgebraicGeometry.IsFinite.{u} ⊓ @Etale.{u} :
        MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.inf
    obtain ⟨W', j, q, hpb⟩ := hπ ⟨W, hW⟩ ζ
    have hkey := presheaf_pullback_snd_of_forall_point B S hS
      (Q := (@_root_.AlgebraicGeometry.IsFinite.{u} ⊓ @Etale.{u} : MorphismProperty Scheme.{u}))
      ξ hξ hcov π (fun y _ r ↦ presheaf_pullback_snd_of_isPullback (sq y r)
        (hbc _ y r ⟨hfin y, het y⟩)) ζ
      (relativelyRepresentable_pullback_snd_of_isPullback B S hS hpb)
    exact ⟨_, q, j, W'.property, (of_presheaf_pullback_snd_of_isPullback B S hS hpb hkey).1, hpb⟩
  · -- Étaleness: every base change of `φ ≫ π` along a morphism from a representable.
    have hE : IsZariskiLocalAtTarget (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
    have := etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
    have hrep₀ : yoneda.relativelyRepresentable (φ ≫ π) :=
      (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := Y)).1
        hY.diagonal_representable (φ ≫ π)
    refine MorphismProperty.relative_of_snd hrep₀ fun W ζ ↦ ?_
    refine of_presheaf_pullback_snd_of_isPullback B S hS (hrep₀.isPullback ζ) ?_
    refine presheaf_pullback_snd_of_forall_point B S hS ξ hξ hcov (φ ≫ π) (fun y b r ↦ ?_) ζ
      (relativelyRepresentable_pullback_snd_of_isPullback B S hS (hrep₀.isPullback ζ))
    have sq₂ := (hφ.rep.isPullback (yoneda.map (pullback.fst (p y) r) ≫ i y)).paste_vert
      (sq y r)
    rw [← Functor.map_comp] at sq₂
    refine presheaf_pullback_snd_of_isPullback sq₂ ?_
    rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _
      (hφ.property_snd (yoneda.map (pullback.fst (p y) r) ≫ i y)) (hbc _ y r (het y))

end AlgebraicGeometry.Space.ProperFlatStein

end
