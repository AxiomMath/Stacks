module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestriction

/-!
# The difference of two sections of `Γ₀`, as a map out of the differentials

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `R₀ = s^{-1}(U₀) ⊆ R` with projection `s₀ : R₀ ⟶ U₀` and inclusion
`j : R₀ ⟶ R`, let `e₀ : U₀ ⟶ R₀` be the unit of the restricted groupoid and let `δ₁, δ₂` be two
elements of the set `Γ₀` of [Stacks Project, Tag 0CKB].

`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalKernel.lean` makes
their difference a `Stacks.Sites.LiftDifferenceData` for the quotient map
`j^♯ : j^{-1}𝒪_R ⟶ 𝒪_{R₀}`.  This file descends that datum to the `𝒪_{U₀}`-linear map

`θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`

of the left hand side of Equation [Stacks Project, Tag 0CKE], and proves the two equations the
equation's derivation is granted: that a section does not differ from itself, and that the
differences along a chain of three sections add up.  Together with
[Stacks Project, Tag 04D0] — the existence of a unique section with a prescribed difference,
which is not proved here — these are the fields of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference`.

The one thing the descent still needs is that the descended difference is a derivation **over
`U₀`**: it must kill the functions read from `U₀` along `s₀`.  That is what
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.descend_structureSharpInverseImage_eq_zero` proves,
and it is where the geometry of the source's argument is spent a second time.  A function read
from `U₀` is, over a covering sieve, read from `U` — because the structure map
`i^♯ : i^{-1}𝒪_U ⟶ 𝒪_{U₀}` of a closed immersion is locally surjective and the inverse image
preserves local surjectivity — and the two readings are identified by the commutative square
`j ≫ s = s₀ ≫ i`; on a function read from `U` the two comorphisms agree, because `δ₁` and `δ₂`
are sections of one and the same morphism `s`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff`: **the
  `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which two elements of `Γ₀` differ**, which
  is the field `diff` of
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictedArrows_square`: the commutative square
  `j ≫ s = s₀ ≫ i`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_app_structureSharpInverseImage_eq`: **a
  function read from `U₀` along `s₀` is, over a covering sieve, the image under `j^♯` of a
  function read from `U` along `j ≫ s`.**
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.descend_structureSharpInverseImage_eq_zero`:
  **the descended difference is a `U₀`-derivation.**
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_self`: **a section does
  not differ from itself**, the field `diff_self`.
* `GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_add_infinitesimalSectionDiff`:
  **the differences along a chain of three sections add up**, the field `diff_add_diff`.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u uu vv

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)

/-- An equation between morphisms of sheaves of commutative rings, read on sections.  Stated
with both sheaves implicit, as
`AlgebraicGeometry.Space.ringSheafHom_congr_app_apply` is. -/
private theorem commRingSheafHom_congr_app_apply {Cc : Type uu} [Category.{vv} Cc]
    {Jc : GrothendieckTopology Cc} {A Bb : Sheaf Jc CommRingCat.{u}} {a b : A ⟶ Bb} (h : a = b)
    (V : Ccᵒᵖ) (z : A.obj.obj V) : a.hom.app V z = b.hom.app V z :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m : A ⟶ Bb => m.hom) h) V) z

/-! ### The commutative square of the restricted groupoid -/

/-- **The commutative square `j ≫ s = s₀ ≫ i`** of the two inclusions, the source and the
restricted source.  It is `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`, which needs
no étale hypothesis. -/
theorem restrictedArrows_square :
    subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) ≫ G.source =
      preimageProjection C S hS G.source U₀ ≫
        subspaceInclusion C S hS G.objects U₀ :=
  conormalEtaleRestrictionSquare C S hS G.source U₀

/-- **The two readings of a function on `U₀` pulled back to `R₀`, on sections.**  The function
read from `U` along `j ≫ s` and the function read from `U₀` along `s₀ ≫ i` are identified by the
square `j ≫ s = s₀ ≫ i` through
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso`; this is that
identification read on a section. -/
theorem app_structureSharpInverseImage_square
    (V : (Space.SmallEtale C S hS
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)ᵒᵖ)
    (w : ToType (((smallEtaleInverseImageRing C S hS
        (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).obj
      (inverseImageStructureSheaf C S hS G.source)).obj.obj V)) :
    (structureSharpInverseImage C S hS (preimageProjection C S hS G.source U₀)).hom.app V
        (((smallEtaleInverseImageRing C S hS
              (preimageProjection C S hS G.source U₀)).map
            (structureSharpInverseImage C S hS
              (subspaceInclusion C S hS G.objects U₀))).hom.app V
          ((smallEtaleRingedToposHom_squareInverseImageRingIso C S hS
            (restrictedArrows_square G U₀)).hom.hom.app V w)) =
      (structureSharpInverseImage C S hS (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).hom.app V
        (((smallEtaleInverseImageRing C S hS
              (subspaceInclusion C S hS G.arrows
                (preimageSubspace C S hS G.source U₀))).map
            (structureSharpInverseImage C S hS G.source)).hom.app V w) :=
  commRingSheafHom_congr_app_apply
    (smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage C S hS
      (restrictedArrows_square G U₀)) V w

/-! ### A function read from `U₀` is locally read from `U` -/

/-- **A function read from `U₀` along `s₀` is, over a covering sieve, the image under `j^♯` of a
function read from `U` along `j ≫ s`.**

The structure map `i^♯ : i^{-1}𝒪_U ⟶ 𝒪_{U₀}` of the closed immersion `i` is locally surjective,
and the inverse image along `s₀` preserves local surjectivity
(`AlgebraicGeometry.Space.isLocallySurjective_inverseImage_structureSharpInverseImage`); so over
a covering sieve the given section is read from `U` along `s₀ ≫ i`, which is `j ≫ s`.  The
identification of the two readings is the commutative square, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.app_structureSharpInverseImage_square`. -/
theorem exists_app_structureSharpInverseImage_eq
    (V : (Space.SmallEtale C S hS
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)ᵒᵖ)
    (σ : ToType ((inverseImageStructureSheaf C S hS
      (preimageProjection C S hS G.source U₀)).obj.obj V)) :
    ∃ T : Sieve V.unop,
      T ∈ Space.SmallEtale.topology C S hS
          (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
            (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1 V.unop ∧
        ∀ ⦃W : Space.SmallEtale C S hS
            (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
              (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1⦄
          (p : W ⟶ V.unop), T p →
          ∃ w : ToType (((smallEtaleInverseImageRing C S hS
              (subspaceInclusion C S hS G.arrows
                (preimageSubspace C S hS G.source U₀))).obj
            (inverseImageStructureSheaf C S hS G.source)).obj.obj (op W)),
            (structureSharpInverseImage C S hS (subspaceInclusion C S hS G.arrows
                  (preimageSubspace C S hS G.source U₀))).hom.app (op W)
                (((smallEtaleInverseImageRing C S hS
                      (subspaceInclusion C S hS G.arrows
                        (preimageSubspace C S hS G.source U₀))).map
                    (structureSharpInverseImage C S hS G.source)).hom.app (op W) w) =
              (structureRingSheaf C S hS
                  (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
                    (preimageSubspace C S hS G.source U₀).2.1⟩ :
                    AlgebraicSpaces C S hS)).obj.map p.op
                ((structureSharpInverseImage C S hS
                  (preimageProjection C S hS G.source U₀)).hom.app V σ) := by
  refine ⟨Presheaf.imageSieve (((smallEtaleInverseImageRing C S hS
      (preimageProjection C S hS G.source U₀)).map
      (structureSharpInverseImage C S hS
        (subspaceInclusion C S hS G.objects U₀))).hom) σ,
    (isLocallySurjective_inverseImage_structureSharpInverseImage C S hS
        (preimageProjection C S hS G.source U₀)
        (subspaceInclusion C S hS G.objects U₀) U₀.2.2).imageSieve_mem σ,
    fun {W} p hp => ?_⟩
  obtain ⟨τ, hτ⟩ := hp
  refine ⟨(smallEtaleRingedToposHom_squareInverseImageRingIso C S hS
      (restrictedArrows_square G U₀)).inv.hom.app (op W) τ, ?_⟩
  have hiso : (smallEtaleRingedToposHom_squareInverseImageRingIso C S hS
          (restrictedArrows_square G U₀)).hom.hom.app (op W)
        ((smallEtaleRingedToposHom_squareInverseImageRingIso C S hS
          (restrictedArrows_square G U₀)).inv.hom.app (op W) τ) = τ :=
    commRingSheafHom_congr_app_apply
      ((smallEtaleRingedToposHom_squareInverseImageRingIso C S hS
        (restrictedArrows_square G U₀)).inv_hom_id) (op W) τ
  refine (app_structureSharpInverseImage_square G U₀ (op W) _).symm.trans ?_
  rw [hiso, hτ]
  exact ConcreteCategory.congr_hom ((structureSharpInverseImage C S hS
    (preimageProjection C S hS G.source U₀)).hom.naturality p.op) σ

/-- **The quotient map `j^♯ : j^{-1}𝒪_R ⟶ 𝒪_{R₀}` is locally surjective**, which is the
hypothesis the descent of [Stacks Project, Tag 0618] is taken under.  It is introduced by name
and never left to instance search: as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSquareZeroValues.lean` record
for left exactness, instance resolution does not find a property of a morphism of sheaves of
rings on the small étale site on its own. -/
theorem isLocallySurjective_restrictedArrowsSharp :
    Sheaf.IsLocallySurjective (structureSharpRingInverseImage C S hS
      (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))) :=
  isLocallySurjective_structureSharpRingInverseImage C S hS
    (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
    (preimageSubspace C S hS G.source U₀).2.2

/-! ### The descended difference is a derivation over `U₀` -/

variable (hU₀ : IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- The difference of the two transported comorphisms vanishes at a function read from `U`
along `j ≫ s`, by
`Space.inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'`:
`δ₁` and `δ₂` are sections of one and the same morphism `s`. -/
theorem infinitesimalSectionLiftDifferenceData_diff_eq_zero
    (δ₁ δ₂ : InfinitesimalSections G U₀)
    (V : (Space.SmallEtale C S hS
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)ᵒᵖ)
    (w : ToType (((smallEtaleInverseImageRing C S hS
        (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).obj
      (inverseImageStructureSheaf C S hS G.source)).obj.obj V)) :
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂).diff
        (((smallEtaleInverseImageRing C S hS
              (subspaceInclusion C S hS G.arrows
                (preimageSubspace C S hS G.source U₀))).map
            (structureSharpInverseImage C S hS G.source)).hom.app V w) = 0 := by
  refine Stacks.Sites.LiftDifferenceData.diff_eq_zero_of_app_eq _ _ ?_
  rw [← app_inverseImage_structureSharpRingInverseImage C S hS
    (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀)) G.source V w]
  exact ringSheafHom_congr_app_apply
    (inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'
      C S hS U₀ (preimageSubspace C S hS G.source U₀) δ₁.1.1 δ₂.1.1 G.source
      (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₁.2)
      (comp_eq_restrictedUnit_comp G U₀ δ₂.2) (δ₁.1.2.trans δ₂.1.2.symm)) V w

include hU₀ in
/-- **The descended difference of the two transported comorphisms is a `U₀`-derivation:** it
kills every function read from `U₀` along `s₀`.

The descent vanishes at a section which lifts, over a covering sieve, to sections the difference
kills (`Stacks.Sites.QuotientDerivation.descend_eq_zero_of_locally_exists`); a function read
from `U₀` lifts over a covering sieve to a function read from `U` along `j ≫ s`, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_app_structureSharpInverseImage_eq`, and the
difference kills those.

This is the field `d_app` of the `U₀`-derivation of `𝒪_{R₀}` which Equation
[Stacks Project, Tag 0619] turns into the `𝒪_{U₀}`-linear map of Equation
[Stacks Project, Tag 0CKE]. -/
theorem descend_structureSharpInverseImage_eq_zero (δ₁ δ₂ : InfinitesimalSections G U₀)
    (V : (Space.SmallEtale C S hS
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)ᵒᵖ)
    (σ : ToType ((inverseImageStructureSheaf C S hS
      (preimageProjection C S hS G.source U₀)).obj.obj V)) :
    letI := isLocallySurjective_restrictedArrowsSharp G U₀
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂).toQuotientDerivation.descend
        ((structureSharpInverseImage C S hS
          (preimageProjection C S hS G.source U₀)).hom.app V σ) = 0 := by
  let := isLocallySurjective_restrictedArrowsSharp G U₀
  obtain ⟨T, hT, hlift⟩ := exists_app_structureSharpInverseImage_eq G U₀ V σ
  refine Stacks.Sites.QuotientDerivation.descend_eq_zero_of_locally_exists _ _ T hT
    fun {W} p hp => ?_
  obtain ⟨w, hw⟩ := hlift p hp
  refine ⟨((smallEtaleInverseImageRing C S hS
      (subspaceInclusion C S hS G.arrows
        (preimageSubspace C S hS G.source U₀))).map
      (structureSharpInverseImage C S hS G.source)).hom.app (op W) w, ?_, ?_⟩
  · exact (structureSharpRingInverseImage_app C S hS
      (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
      (op W) _).trans hw
  · exact infinitesimalSectionLiftDifferenceData_diff_eq_zero G U₀ hU₀ δ₁ δ₂ (op W) w

include hU₀ in
/-- The first of the two transported comorphisms of the datum, as a `rfl` equation: the
projection is crossed once, in a statement small enough for the kernel to do it. -/
theorem infinitesimalSectionLiftDifferenceData_f (δ₁ δ₂ : InfinitesimalSections G U₀) :
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂).f =
      restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        δ₁.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₁.2) := rfl

include hU₀ in
/-- The second of the two transported comorphisms of the datum, as a `rfl` equation. -/
theorem infinitesimalSectionLiftDifferenceData_g (δ₁ δ₂ : InfinitesimalSections G U₀) :
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂).g =
      restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
        δ₂.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ₂.2) := rfl

/-! ### The difference, as a map out of the differentials -/

include hU₀ in
/-- **The `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which two elements of `Γ₀`
differ.**  The difference of their two transported comorphisms, descended along the locally
surjective `j^♯ : j^{-1}𝒪_R ⟶ 𝒪_{R₀}` to a `U₀`-derivation of `𝒪_{R₀}` with values in
`(e₀)_*𝒞_{U₀/U}` and transposed by Equation [Stacks Project, Tag 0619].

This is [Stacks Project, Tag 0618] with Equation (0619) in the groupoid situation, and the field
`diff` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference`. -/
noncomputable def infinitesimalSectionDiff (δ₁ δ₂ : InfinitesimalSections G U₀) :
    InfinitesimalSectionsHom G U₀ :=
  letI := isLocallySurjective_restrictedArrowsSharp G U₀
  liftDifferenceDifferentialsHom C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₁ δ₂)

include hU₀ in
/-- The defining equation of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff`, so that consumers
rewrite with it rather than make the kernel unfold the definition inside a sum. -/
theorem infinitesimalSectionDiff_eq (δ₁ δ₂ : InfinitesimalSections G U₀) :
    infinitesimalSectionDiff G U₀ hU₀ δ₁ δ₂ =
      letI := isLocallySurjective_restrictedArrowsSharp G U₀
      liftDifferenceDifferentialsHom C S hS (preimageProjection C S hS G.source U₀)
        (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
        (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂)
        (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₁ δ₂) := rfl

include hU₀ in
/-- **A section of `Γ₀` does not differ from itself**, the field `diff_self`: the two
transported comorphisms are then one and the same morphism. -/
theorem infinitesimalSectionDiff_self (δ : InfinitesimalSections G U₀) :
    infinitesimalSectionDiff G U₀ hU₀ δ δ = 0 :=
  let := isLocallySurjective_restrictedArrowsSharp G U₀
  liftDifferenceDifferentialsHom_eq_zero C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ δ)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ δ)
    ((infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ δ).trans
      (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ δ).symm)

include hU₀ in
/-- **The differences along a chain of three sections of `Γ₀` add up**, the field
`diff_add_diff`: the three pairs of transported comorphisms are `(f₁, f₂)`, `(f₂, f₃)` and
`(f₁, f₃)` in one and the same square-zero ideal, so
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_add` applies with all three index
equations holding by definition. -/
theorem infinitesimalSectionDiff_add_infinitesimalSectionDiff
    (δ₁ δ₂ δ₃ : InfinitesimalSections G U₀) :
    infinitesimalSectionDiff G U₀ hU₀ δ₁ δ₂ + infinitesimalSectionDiff G U₀ hU₀ δ₂ δ₃ =
      infinitesimalSectionDiff G U₀ hU₀ δ₁ δ₃ := by
  rw [infinitesimalSectionDiff_eq G U₀ hU₀ δ₁ δ₂,
    infinitesimalSectionDiff_eq G U₀ hU₀ δ₂ δ₃,
    infinitesimalSectionDiff_eq G U₀ hU₀ δ₁ δ₃]
  let := isLocallySurjective_restrictedArrowsSharp G U₀
  exact liftDifferenceDifferentialsHom_add C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₂)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₂ δ₃)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ δ₁ δ₃)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₁ δ₂)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₂ δ₃)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ δ₁ δ₃)
    ((infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ₁ δ₂).trans
      (infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ₂ δ₃).symm)
    ((infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ₁ δ₂).trans
      (infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ δ₁ δ₃).symm)
    ((infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ₂ δ₃).trans
      (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ δ₁ δ₃).symm)

include hU₀ in
/-- **`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference` from the one
input which is not proved here.**  Four of its five fields are discharged above: `U` is a first
order thickening of `U₀` by hypothesis, the difference of two elements of `Γ₀` is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff`, a section does not
differ from itself and the differences along a chain of three sections add up.

What remains is the field `existsUnique_diff`, that every `𝒪_{U₀}`-linear map is the difference
from a given section of exactly one section.  That is [Stacks Project, Tag 04D0] in this
situation; it rests on the action of [Stacks Project, Tag 0CK6], hence on
[Stacks Project, Tag 05ZN] and so on Properties of Spaces, Theorem 04KL, which this development
carries as a hypothesis (`AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification`).
It is taken here as the argument `hex`. -/
noncomputable def infinitesimalSectionDifferenceOfExistsUnique
    (hex : ∀ (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀),
      ∃! ε : InfinitesimalSections G U₀, infinitesimalSectionDiff G U₀ hU₀ δ ε = θ) :
    InfinitesimalSectionDifference G U₀ where
  firstOrder := hU₀
  diff := infinitesimalSectionDiff G U₀ hU₀
  diff_self := infinitesimalSectionDiff_self G U₀ hU₀
  diff_add_diff := infinitesimalSectionDiff_add_infinitesimalSectionDiff G U₀ hU₀
  existsUnique_diff := hex

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
