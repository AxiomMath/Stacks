module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.UniversallyClosedAffineSpaceTest
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Testing properness on finitely presented bases and on affine spaces

Let `f : X ⟶ Y` be a separated morphism of finite type between algebraic spaces over a scheme
`S`. Tag 0CMA says that properness of `f` is detected by the same two small families of base
changes that detect universal closedness in Tag 0CM9: those along the morphisms `Z ⟶ Y` which
are locally of finite presentation, and those along the projections `𝐀ⁿ × V ⟶ Y` attached to
one surjective étale scheme atlas `V ⟶ Y` of the target.

## Main results

* `AlgebraicGeometry.Space.isClosedMorphism_pullback_fst_of_isProper`: a proper morphism has
  closed base changes along the morphisms locally of finite presentation.
* `AlgebraicGeometry.Space.exists_affineSpaceTest_of_isProper`: a proper morphism passes the
  affine-space test over some surjective étale scheme atlas of the target.
* `AlgebraicGeometry.Space.isProper_of_isClosedMorphism_pullback_fst`: a separated morphism of
  finite type whose base changes along the morphisms locally of finite presentation are closed
  is proper.
* `AlgebraicGeometry.Space.isProper_of_affineSpaceTest`: a separated morphism of finite type
  passing the affine-space test over one surjective étale scheme atlas of the target is proper.
* `AlgebraicGeometry.Space.isProper_tfae_of_isSeparated_of_isFiniteType`: the three equivalent
  conditions of Tag 0CMA.

## Implementation notes

A proper morphism is by definition a separated morphism of finite type which is universally
closed, Tag 03ZM, `AlgebraicGeometry.Space.IsProper`; and a morphism of finite type is by
definition locally of finite type and quasi-compact, Tag 03XF,
`AlgebraicGeometry.Space.IsFiniteType`. Under the standing hypotheses of this tag the two
conditions tested below are therefore literally the conditions tested in Tag 0CM9 for universal
closedness, and the quasi-compactness that Tag 0CM9 requires of `f` is not an extra assumption
but the second conjunct of finite type. Each statement here is accordingly the corresponding
statement of Tag 0CM9 with separatedness and finite type carried along unchanged, which is the
proof of the source: it deduces the lemma from Tag 0CM9 by unfolding properness.

The separatedness and finite type hypotheses are the standing hypotheses of the source, so the
implications into properness carry them explicitly. They are not what is at stake in those
implications: universal closedness, the one conjunct of properness that is not assumed, is in
each case derived from the stated test through Tag 0CM9.

The source states the second condition as a quantification over the morphisms `Y ⟶ Z` locally
of finite presentation, but the fibre product `X ×_Y Z` appearing in the same clause requires a
morphism `Z ⟶ Y`; the direction is a slip in the source, and Tag 0CM9, of which the source
declares this lemma a special case, states the clause over the morphisms `Z ⟶ Y`. That is the
reading formalized here.

## References

* [Stacks Project, Tag 0CMA](https://stacks.math.columbia.edu/tag/0CMA)
* [Stacks Project, Tag 0CM9](https://stacks.math.columbia.edu/tag/0CM9)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_properAffineSpaceTest
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The two implications out of properness -/

/-- **Stacks 0CMA, (1) implies (2).** The base change of a proper morphism of algebraic spaces
over `S` along a morphism which is locally of finite presentation is closed.

A proper morphism is universally closed, so this is the corresponding implication of Tag
0CM9. -/
@[stacks 0CMA "(1) implies (2)"]
theorem isClosedMorphism_pullback_fst_of_isProper (f : X ⟶ Y) (hf : IsProper B S hS f)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z) (h : Z ⟶ Y)
    (hh : IsLocallyOfFinitePresentation B S hS h) :
    IsClosedMorphism B S hS (pullback.fst h f) :=
  isClosedMorphism_pullback_fst_of_universallyClosed B S hS f hf.2.2 hZ h hh

/-- **Stacks 0CMA, (1) implies (3).** A proper morphism of algebraic spaces over `S` passes the
affine-space test over a surjective étale scheme atlas of its target: for every `n` the base
change of `f` along affine `n`-space over the atlas is closed.

A proper morphism is universally closed, so this is the corresponding implication of Tag
0CM9. -/
@[stacks 0CMA "(1) implies (3)"]
theorem exists_affineSpaceTest_of_isProper (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsProper B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧
        ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a ∧
          IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f) :=
  exists_affineSpaceTest_of_universallyClosed B S hS hY f hf.2.2

/-! ### The two implications into properness -/

/-- **Stacks 0CMA, (2) implies (1).** A separated morphism of finite type between algebraic
spaces over `S` whose base changes along the morphisms locally of finite presentation are
closed is proper.

Properness is separatedness, finite type and universal closedness; the first two are the
standing hypotheses and the third is supplied by Tag 0CM9, whose quasi-compactness hypothesis
is the second conjunct of finite type. -/
@[stacks 0CMA "(2) implies (1)"]
theorem isProper_of_isClosedMorphism_pullback_fst (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (hft : IsFiniteType B S hS f)
    (htest : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
      ∀ h : Z ⟶ Y, IsLocallyOfFinitePresentation B S hS h →
        IsClosedMorphism B S hS (pullback.fst h f)) :
    IsProper B S hS f :=
  ⟨hsep, hft, universallyClosed_of_isClosedMorphism_of_isLocallyOfFinitePresentation
    B S hS hX hY f hft.2 htest⟩

/-- **Stacks 0CMA, (3) implies (1).** A separated morphism of finite type between algebraic
spaces over `S` which passes the affine-space test over one surjective étale scheme atlas of
its target is proper.

The affine-space test gives closedness of the base changes along the morphisms locally of
finite presentation, by Tag 0CM9, and that in turn gives universal closedness. -/
@[stacks 0CMA "(3) implies (1)", ega "II 5.6.3" "more general"]
theorem isProper_of_affineSpaceTest (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (hft : IsFiniteType B S hS f) (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (hgsurj : IsSurjective B S hS g) (hgetale : IsEtale B S hS g)
    (htest : ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a ∧
      IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f)) :
    IsProper B S hS f :=
  isProper_of_isClosedMorphism_pullback_fst B S hS hX hY f hsep hft fun _Z hZ h hh ↦
    isClosedMorphism_pullback_fst_of_affineSpaceTest B S hS hX hY f V g hgsurj hgetale htest
      hZ h hh

/-! ### Stacks 0CMA -/

/-- **Stacks 0CMA.** For a separated morphism `f : X ⟶ Y` of finite type between algebraic
spaces over `S` the following are equivalent: `f` is proper; the base change of `f` along every
morphism to `Y` which is locally of finite presentation is closed; and there is a surjective
étale morphism to `Y` from a presheaf represented by an object `V` of the site such that for
every `n` the base change of `f` along affine `n`-space over `V` is closed.

This is the special case of Tag 0CM9 obtained by unfolding properness into separatedness,
finite type and universal closedness. -/
@[stacks 0CMA]
theorem isProper_tfae_of_isSeparated_of_isFiniteType (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (hft : IsFiniteType B S hS f) :
    List.TFAE
      [IsProper B S hS f,
        ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
          ∀ h : Z ⟶ Y, IsLocallyOfFinitePresentation B S hS h →
            IsClosedMorphism B S hS (pullback.fst h f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
              IsAffineSpaceOver B S hS V W n a ∧
                IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f)] := by
  tfae_have 1 → 2 := fun hf Z hZ h hh ↦
    isClosedMorphism_pullback_fst_of_isProper B S hS f hf hZ h hh
  tfae_have 2 → 1 := fun h ↦
    isProper_of_isClosedMorphism_pullback_fst B S hS hX hY f hsep hft h
  tfae_have 1 → 3 := fun hf ↦ exists_affineSpaceTest_of_isProper B S hS hY f hf
  tfae_have 3 → 1 := by
    rintro ⟨V, g, hgsurj, hgetale, htest⟩
    exact isProper_of_affineSpaceTest B S hS hX hY f hsep hft V g hgsurj hgetale htest
  tfae_finish

end AlgebraicGeometry.Space

end
