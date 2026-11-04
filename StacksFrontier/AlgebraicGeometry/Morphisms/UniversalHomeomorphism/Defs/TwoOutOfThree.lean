module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# The two-out-of-three property for universal homeomorphisms

For composable morphisms of schemes, if any two among the two morphisms and their composite
are universal homeomorphisms, then so is the third.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_hasTwoOutOfThreeProperty` states that universal
  homeomorphisms satisfy the two-out-of-three property.

## Implementation notes

The three cases are bundled using Mathlib's `MorphismProperty.HasTwoOutOfThreeProperty`
applied to `AlgebraicGeometry.UniversalHomeomorphism`.

## References

* [Stacks Project, Tag 0H2M](https://stacks.math.columbia.edu/tag/0H2M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

private instance : (topologically @IsHomeomorph).RespectsIso :=
  topologically_respectsIso (P := @IsHomeomorph) (fun e => e.isHomeomorph)
    (fun _ _ hf hg => hg.comp hf)

/-- A morphism all of whose base changes along morphisms into its target are homeomorphisms
on underlying spaces is a universal homeomorphism. -/
private lemma universalHomeomorphism_of_pullbackHomeomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ {T : Scheme.{u}} (i : T ⟶ Y),
      IsHomeomorph (pullback.fst i f).base) :
    UniversalHomeomorphism f := by
  rw [universalHomeomorphism_iff]
  exact MorphismProperty.universally_mk' _ f fun i _ => hf i

/-- If `f` and `f ≫ g` are homeomorphisms on underlying spaces, then so is `g`. -/
private lemma isHomeomorph_of_comp_left
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsHomeomorph f.base)
    (hfg : IsHomeomorph (f ≫ g).base) :
    IsHomeomorph g.base := by
  let e := hf.homeomorph f.base
  let k := hfg.homeomorph (f ≫ g).base
  have heq : g.base = k ∘ e.symm := by
    funext y
    simpa [e, k, Scheme.Hom.comp_base] using (congrArg g.base (e.apply_symm_apply y)).symm
  rw [heq]
  exact k.isHomeomorph.comp e.symm.isHomeomorph

/-- If `g` and `f ≫ g` are homeomorphisms on underlying spaces, then so is `f`. -/
private lemma isHomeomorph_of_comp_right
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsHomeomorph g.base)
    (hfg : IsHomeomorph (f ≫ g).base) :
    IsHomeomorph f.base := by
  let e := hg.homeomorph g.base
  let k := hfg.homeomorph (f ≫ g).base
  have heq : f.base = e.symm ∘ k := by
    funext x
    simpa [e, k, Scheme.Hom.comp_base] using (e.symm_apply_apply (f.base x)).symm
  rw [heq]
  exact e.symm.isHomeomorph.comp k.isHomeomorph

/-- If `f` and `f ≫ g` are universal homeomorphisms, then so is `g`. -/
private lemma universalHomeomorphism_of_comp_of_universalHomeomorphism
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UniversalHomeomorphism f)
    (hfg : UniversalHomeomorphism (f ≫ g)) :
    UniversalHomeomorphism g := by
  apply universalHomeomorphism_of_pullbackHomeomorphisms g
  intro T β
  have hfpb : IsPullback (pullback.fst (pullback.snd β g) f)
      (pullback.snd (pullback.snd β g) f) (pullback.snd β g) f := IsPullback.of_hasPullback _ _
  exact isHomeomorph_of_comp_left _ _ (hf.universally_isHomeomorph _ _ _ hfpb)
    (hfg.universally_isHomeomorph _ _ _ (hfpb.paste_horiz (IsPullback.of_hasPullback _ _)))

/-- A section of a morphism which is a homeomorphism on underlying spaces is a universal
homeomorphism. -/
private lemma section_of_universalHomeomorphism_isUniversalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hf : IsHomeomorph f.base) (hs : s ≫ f = 𝟙 Y) :
    UniversalHomeomorphism s := by
  have hAff : IsAffineHom f :=
    isAffineHom_of_isInducing f hf.isInducing (by
      rw [Set.range_eq_univ.mpr hf.bijective.2]
      exact isClosed_univ)
  have : IsSeparated f := IsSeparated.of_isAffineHom f
  have : IsClosedImmersion (s ≫ f) := by
    simpa [hs] using (inferInstance : IsClosedImmersion (𝟙 Y))
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  have hleft (x : Y) : f (s x) = x := by
    simpa using congrArg (fun q : Y ⟶ Y => q x) hs
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective]
  refine ⟨?_, ?_, ⟨fun x => ⟨f x, hf.injective (hleft (f x))⟩⟩⟩
  · infer_instance
  · have : Mono s := inferInstance
    infer_instance

/-- If `g` and `f ≫ g` are universal homeomorphisms, then so is `f`. -/
private lemma universalHomeomorphism_of_postcomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : UniversalHomeomorphism g)
    (hfg : UniversalHomeomorphism (f ≫ g)) :
    UniversalHomeomorphism f := by
  have hγ : UniversalHomeomorphism (pullback.lift (𝟙 X) f (by simp) : X ⟶ pullback (f ≫ g) g) :=
    section_of_universalHomeomorphism_isUniversalHomeomorphism (pullback.fst _ _) _
      (hg.universally_isHomeomorph _ _ _ (IsPullback.of_hasPullback _ _)) (pullback.lift_fst _ _ _)
  have h := universalHomeomorphism_comp _ _ hγ
    ⟨(topologically @IsHomeomorph).universally.pullback_snd _ _ hfg.1⟩
  rwa [pullback.lift_snd] at h

/-- Universal homeomorphisms of schemes satisfy the two-out-of-three property. -/
@[stacks 0H2M]
instance universalHomeomorphism_hasTwoOutOfThreeProperty :
    MorphismProperty.HasTwoOutOfThreeProperty
      (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) where
  comp_mem f g hf hg := universalHomeomorphism_comp f g hf hg
  of_postcomp f g hg hfg := universalHomeomorphism_of_postcomp f g hg hfg
  of_precomp f g hf hfg := universalHomeomorphism_of_comp_of_universalHomeomorphism f g hf hfg

end AlgebraicGeometry

end
