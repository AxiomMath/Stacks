module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothAlgebra

/-!
# Descent of smoothness along a surjective flat morphism

Let `X ⟶ Y ⟶ S` be morphisms of schemes with `X ⟶ Y` surjective, flat and locally of finite
presentation. If the composition `X ⟶ S` is smooth, then so is `Y ⟶ S`. In particular smoothness
descends along a surjective smooth morphism.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Smooth.smooth_of_comp_of_fppf` descends smoothness along a surjective flat morphism
  which is locally of finite presentation.
* `Stacks.Smooth.smooth_of_comp_surjective_smooth` descends smoothness along a surjective smooth
  morphism.

## Implementation notes

The source's commutative triangle is expressed by taking its morphism from `X` to `S` to be the
composite `f ≫ q`; this is equivalent to the formulation with a separately given `p : X ⟶ S`
and an equality `p = f ≫ q`.

Smoothness is `AlgebraicGeometry.Smooth`, whose defining condition is a property of the maps
`Γ(S, V) ⟶ Γ(Y, U)` for affine opens `U ⊆ Y` and `V ⊆ S` with `q(U) ⊆ V`. The statement is
therefore proved by restricting the whole situation to such a pair, which is the content of
`Scheme.Hom.resLE`: the restriction of `f` over `U` stays surjective, flat and locally of finite
presentation, and the restriction of `f ≫ q` is the composite of the two restrictions by
`Scheme.Hom.resLE_comp_resLE`.

With `Y` and `S` affine the morphism `f` is replaced by an affine one. Since `f` is flat and
locally of finite presentation it is open, so its image already comes from a quasi-compact open
`W ⊆ X` (`IsOpenMap.exists_opens_image_eq_of_prespectralSpace`), and `W` is dominated by an
affine scheme through a smooth morphism because smoothness is Zariski-local at the source and
contains the identities (`Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`). The resulting
`g : T ⟶ Y` with `T` affine is surjective, flat and locally of finite presentation, and `g ≫ q`
is smooth as soon as `f ≫ q` is, because the morphism `T ⟶ X` is smooth. For affine schemes
the surjectivity and flatness of `g` are the faithful flatness of `Γ(Y) ⟶ Γ(T)`
(`Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`), so the affine case is exactly the
algebra statement `Stacks.RingTheory.SmoothDescent.ringHom_smooth_of_faithfullyFlat`.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

variable {X Y S : Scheme.{u}}

/-- A surjective flat morphism locally of finite presentation onto an affine scheme is dominated
by an affine scheme through a smooth morphism: the image of a quasi-compact open `W ⊆ X` is
already all of `Y`, and `W` is covered by finitely many affine opens. -/
private theorem exists_affine_smooth_cover (f : X ⟶ Y) [IsAffine Y] [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] :
    ∃ (T : Scheme.{u}) (h : T ⟶ X), IsAffine T ∧ Smooth h ∧ Surjective (h ≫ f) := by
  obtain ⟨W : X.Opens, hW, hWsurj⟩ :=
    f.isOpenMap.exists_opens_image_eq_of_prespectralSpace f.continuous (by simp) isOpen_univ
      isCompact_univ
  have : CompactSpace (Scheme.Opens.toScheme W) := isCompact_iff_compactSpace.mp hW
  have : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  have : MorphismProperty.ContainsIdentities (@Smooth.{u}) :=
    HasRingHomProperty.containsIdentities
      RingHom.Smooth.holdsForLocalizationAway.containsIdentities
  obtain ⟨T, hT, hTsurj, hTsm, hTaff⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource
      @Smooth.{u} (Scheme.Opens.toScheme W)
  have : Smooth hT := hTsm
  have : Surjective hT := hTsurj
  have hWf : Surjective (Scheme.Opens.ι W ≫ f) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x, hxW, hxy⟩ : y ∈ f.base '' W := by rw [hWsurj]; trivial
    exact ⟨⟨x, hxW⟩, hxy⟩
  refine ⟨T, hT ≫ Scheme.Opens.ι W, hTaff, inferInstance, ?_⟩
  simpa only [Category.assoc] using
    (show Surjective (hT ≫ (Scheme.Opens.ι W ≫ f)) from inferInstance)

/-- The affine case of the descent: with `Y` and `S` affine, the statement is the algebra
statement for the global sections of an affine cover of `X`. -/
private theorem smooth_of_comp_of_fppf_affine (f : X ⟶ Y) (q : Y ⟶ S) [IsAffine Y] [IsAffine S]
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Smooth (f ≫ q)] : Smooth q := by
  obtain ⟨T, h, hT, hh, hs⟩ := exists_affine_smooth_cover f
  have : IsAffine T := hT
  have : Smooth h := hh
  have : Surjective (h ≫ f) := hs
  have hsm : Smooth ((h ≫ f) ≫ q) := by
    rw [Category.assoc]
    infer_instance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  refine Stacks.RingTheory.SmoothDescent.ringHom_smooth_of_faithfullyFlat q.appTop.hom
    (h ≫ f).appTop.hom ?_
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (h ≫ f)).mp ⟨inferInstance, hs⟩)
    (HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) (h ≫ f) inferInstance)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
    HasRingHomProperty.appTop (P := @Smooth) ((h ≫ f) ≫ q) hsm

/-- **Stacks Project, Tag 05B5 (smooth case).** Smoothness descends along a surjective flat
morphism which is locally of finite presentation: if `f : X ⟶ Y` is surjective, flat and locally
of finite presentation and `f ≫ q` is smooth, then `q : Y ⟶ S` is smooth. -/
@[stacks 05B5 "smooth_permanence"]
theorem smooth_of_comp_of_fppf (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] [Smooth (f ≫ q)] : Smooth q := by
  refine ⟨?_⟩
  intro V hV U hU e
  let f' := f.resLE U (f ⁻¹ᵁ U) le_rfl
  let q' := q.resLE V U e
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Surjective f' := surjective_resLE f U
  have : Flat f' := by dsimp only [f']; infer_instance
  have : LocallyOfFinitePresentation f' := by dsimp only [f']; infer_instance
  have : Smooth (f' ≫ q') := by
    show Smooth (f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ q.resLE V U e)
    rw [Scheme.Hom.resLE_comp_resLE]
    infer_instance
  have hq' := smooth_of_comp_of_fppf_affine f' q'
  have hq'app := hq'.smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
  dsimp only [q'] at hq'app
  rw [Scheme.Hom.resLE_appLE q e ⊤ ⊤ (by simp)] at hq'app
  exact (q.appLE_congr e (by simp) (by simp) (fun φ => φ.hom.Smooth)).mpr hq'app

/-- **Stacks Project, Tag 02KM (smooth case).** If `f` is surjective and smooth and `f ≫ q` is
smooth, then `q` is smooth.

This is also Stacks 02K5: there the target of `f ≫ q` is additionally assumed locally of finite
presentation, which that source's own footnote observes is implied by the other hypotheses. -/
@[stacks 02KM "smooth_case", stacks 02K5]
theorem smooth_of_comp_surjective_smooth (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Smooth f]
    [Smooth (f ≫ q)] : Smooth q :=
  smooth_of_comp_of_fppf f q

end Stacks.Smooth

end
