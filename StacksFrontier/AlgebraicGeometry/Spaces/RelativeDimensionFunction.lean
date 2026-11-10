module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
public import StacksFrontier.Topology.Dimension.DimensionFunction

/-!
# The dimension function of a decent space of finite type over a scheme (Stacks 0ED5)

Let `S` be a locally Noetherian, universally catenary scheme carrying a dimension function
`δ`, let `X` be a decent algebraic space over `S` whose structure morphism `f : X → S` is
locally of finite type, and let `δ_X` send a point `x` of `|X|` to `δ (f x)` plus the
transcendence degree of `x` over `f x`. Stacks 0ED5 says `δ_X` is a dimension function
on `|X|`. The function `δ_X` is `AlgebraicGeometry.Space.inducedDimensionValue`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_specialization_lift_of_isDecentSpace` is Stacks 03IL:
  along an étale chart of a *decent* algebraic space every generalization of a point lifts.
* `AlgebraicGeometry.Space.generalizingMap_pointsMap_of_isDecentSpace` is the same statement
  read as Mathlib's `GeneralizingMap`.
* `TopologicalSpace.exists_dimensionFunction_of_generalizingMap`: a function whose
  composition with a continuous, surjective, *generalizing* map is a dimension function is a
  dimension function.
* `AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue_of_isDecentSpace`
  is Stacks 0ED5, with Stacks 02JW carried as an explicit named hypothesis.

## Implementation notes

**The hypothesis `h02JW`.** The one input of Stacks 0ED5 not proved here is Morphisms,
Lemma 02JW: the corresponding statement for a morphism of *schemes* locally of finite type
over a locally Noetherian universally catenary base. It belongs to Chapter 29 and
is carried as the explicit hypothesis `h02JW`, whose statement is 02JW's conclusion verbatim
for the base scheme and dimension function at hand, under 02JW's own hypotheses
(`IsLocallyNoetherian` and `AlgebraicGeometry.Scheme.IsUniversallyCatenary`, both retained as
hypotheses of the theorem so that `h02JW` is dischargeable from Stacks 02JW; the proof itself
uses neither of them, nor would it use them if `h02JW` were replaced by a proof of 02JW, since
they are consumed inside that proof). Because the main theorem
carries that hypothesis it deliberately takes **no** `@[stacks]` attribute; the attribute it
would carry given a proof of 02JW is `@[stacks 0ED5]`.

**How the source's two topological inputs are used, and how one of them is avoided.** The
proof fixes a surjective étale chart `φ : U ⟶ X` with `U` a scheme and compares `δ_X` with
the function `δ_U` of 02JW for the composite `U → X → S`. The source then invokes Lemma 03IL
to lift a specialization of `|X|` to one of `|U|`, and Lemma 03K5 — two points of `|U|` over
one point of `|X|` in a specialization relation are equal — to see that the lifted
specialization is immediate whenever the original is.

03IL is proved here, from Stacks 03K2
(`AlgebraicGeometry.Space.exists_specialization_lift_of_finite_etale_fibers`) and the
implication 03JV (4) ⟹ (1), which in the namespace `AlgebraicGeometry.Space` is
`HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnEveryAffineEtaleChart`.
This is exactly the source's "combine 03JX and 03K2". **03K5 is not used and is not
needed.** In its place the proof uses the strict drop of `δ_U` itself: an intermediate point
`z` of the lifted specialization has image `x` or `x'` by immediateness downstairs, and
either value makes `δ_U` drop strictly from `δ_X x` to `δ_X x` respectively from `δ_X x'` to
`δ_X x'`, which is absurd. This is the same substitution that
`AlgebraicGeometry.Space.exists_dimensionFunction_of_isFinite` makes for Lemma 0ACK in the
proof of Stacks 0ED9, and it means neither 03K5 nor 03IM nor 03JS is required. Tag 03K5 is
separately available in the library as
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_isDecentSpace`; it is not
imported here, because the strict-drop argument makes it unnecessary.

**The topological statement is the exact dual of the specializing one.**
`TopologicalSpace.exists_dimensionFunction_of_specializingMap` descends the property of
being a dimension function along a continuous surjection which lifts *specializations*; here
the chart map lifts *generalizations*, so the dual statement is proved, with `SpecializingMap`
replaced by Mathlib's `GeneralizingMap`. The two are genuinely different hypotheses, and
neither follows from openness: a continuous open surjection need not be generalizing. For a
witness take `Y` the Sierpiński space `{g, s}` with `g ⤳ s`, and `X = ℕ ∪ {∞}` topologized by
the arbitrary subsets of `ℕ` together with the sets `U ∪ {∞}` for `U` cofinite in `ℕ`, with
`f` sending `ℕ` to `g` and `∞` to `s`. This `f` is continuous, open and surjective, and `∞`
lies in the closure of `ℕ` but in the closure of no single `n`, so the generalization
`g ⤳ f ∞` does not lift. That is why decency of `X` is consumed here while the specializing
statement consumes no hypothesis on either space at all.

**Why the base is an object of the site.** The source's base is a scheme, and the induced
function is stated for a morphism of presheaves, so the base appears here as `yoneda.obj T`
for an object `T` of the big fppf site over `S`. Taking `T`
to be the terminal object, whose underlying scheme is `S`, recovers the source's statement;
a general `T` is a generalization of it. The dimension function `δ` is a
`TopologicalSpace.DimensionFunction` of the underlying *scheme* of `T`, as in the source, and
is transported to the points of `yoneda.obj T` along
`AlgebraicGeometry.Space.pointsEquivScheme`.

**The comparison of the two functions.** That `δ_U(u) = δ_X(φ(u))` is, in the source, "the
definition of relative transcendence degree". Here it is
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_pointsMap_iff`, which reads the relative
transcendence degree of Tag 04NM off the single commuting square of étale charts `φ` over the
identity of `yoneda.obj T`; the resulting value is the residue-field transcendence degree of
the underlying scheme morphism, which is the quantity 02JW's function uses.
`Cardinal.toNat_toENat` reconciles the two truncations. Stacks 06RX, invariance of the
relative transcendence degree under a locally quasi-finite first factor, is therefore *not*
needed: the chart equation does the same work directly, with no second factorization.

**The 0ACA/0ACK source defect is avoided.** As for
`AlgebraicGeometry.Space.exists_dimensionFunction_of_isFinite`, nothing here routes through
Stacks 0ACA or 0ACK, whose condition (3) is not equivalent to the others; the strict-drop
substitution described above is what removes the need for them.

## References

* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0ED5](https://stacks.math.columbia.edu/tag/0ED5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopologicalSpace

/-- **A function whose pullback along a generalizing surjection is a dimension function is a
dimension function.** Let `g : X → Y` be continuous, surjective and generalizing — for
instance the map on points of a surjective étale chart of a decent algebraic space — and let
`δ : Y → ℤ` be such that `δ ∘ g` is a dimension function on `X`. Then `δ` is a dimension
function on `Y`.

This is the exact dual of
`TopologicalSpace.exists_dimensionFunction_of_specializingMap`. For a non-trivial
specialization `y ⤳ y'` pick `x'` above `y'` and lift to `x ⤳ x'` with `g x = y`; the two
images differ, so `δ ∘ g` drops strictly. If moreover `y ⤳ y'` is immediate then so is
`x ⤳ x'`: an intermediate `z` has `g z ∈ {y, y'}`, and `g z = y` forces `z = x` while
`g z = y'` forces `z = x'`, since otherwise `δ ∘ g` would have to drop strictly from `δ y` to
`δ y` respectively from `δ y'` to `δ y'`. -/
theorem exists_dimensionFunction_of_generalizingMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hcont : Continuous g) (hsurj : Function.Surjective g)
    (hgen : GeneralizingMap g) (δ : Y → ℤ) (d : DimensionFunction X)
    (hd : ∀ x : X, d x = δ (g x)) :
    ∃ e : DimensionFunction Y, ∀ y : Y, e y = δ y := by
  rw [exists_dimensionFunction_iff]
  have key : ∀ a b : X, a ⤳ b → g a = g b → a = b := fun a b hab hg =>
    by_contra fun hne => by simpa [hd, hg] using d.strictAnti_specializes hab hne
  refine ⟨fun y y' hyy' hne => ?_, fun y y' himm => ?_⟩
  · obtain ⟨x', rfl⟩ := hsurj y'
    obtain ⟨x, hxx', rfl⟩ := hgen hyy'
    simpa only [hd] using d.strictAnti_specializes hxx' fun he => hne (congrArg g he)
  · obtain ⟨x', rfl⟩ := hsurj y'
    obtain ⟨x, hxx', rfl⟩ := hgen himm.1
    simpa only [hd] using d.step_immediate ⟨hxx', fun he => himm.2.1 (congrArg g he),
      fun z hz hz' => (himm.2.2 (g z) (hz.map hcont) (hz'.map hcont)).imp
        (fun h => (key x z hz h.symm).symm) (key z x' hz')⟩

end TopologicalSpace

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

open TopologicalSpace

/-- **Stacks 03IL.** Let `X` be a decent algebraic space over a scheme `S` and let `x, x'` be
points of `|X|` with `x' ⤳ x`, that is, `x` a specialization of `x'`. Then for every étale
`φ : h_U ⟶ X` with `U` an object of the site and every point `p` of `|U|` above `x` there is a
point `p' ⤳ p` of `|U|` above `x'`.

This is the source's "combine 03JX and 03K2": decency is condition (4) of Stacks 03JV at
every point, which gives condition (1) at `x'` by, in this namespace,
`HasQuasiCompactMonomorphicFieldRepresentative.hasFiniteFibresOnEveryAffineEtaleChart`, and
that is the hypothesis of
`AlgebraicGeometry.Space.exists_specialization_lift_of_finite_etale_fibers`. -/
@[stacks 03IL]
theorem exists_specialization_lift_of_isDecentSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (x x' : points B S hS X) (hs : x' ⤳ x)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (p : points B S hS (yoneda.obj U)) (hp : pointsMap B S hS (yoneda.obj U) φ p = x) :
    ∃ p' : points B S hS (yoneda.obj U),
      p' ⤳ p ∧ pointsMap B S hS (yoneda.obj U) φ p' = x' :=
  exists_specialization_lift_of_finite_etale_fibers B S hS X hX x x' hs
    ((hXdec x').hasFiniteFibresOnEveryAffineEtaleChart B S hS X hX) U φ hφ p hp

/-- **Stacks 03IL as a generalizing map.** The map on points of an étale chart of a decent
algebraic space lifts generalizations, which is Mathlib's `GeneralizingMap`. -/
theorem generalizingMap_pointsMap_of_isDecentSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ) :
    GeneralizingMap (pointsMap B S hS (yoneda.obj U) φ) := fun {p} {y} hy =>
  exists_specialization_lift_of_isDecentSpace B S hS X hX hXdec _ y hy U φ hφ p rfl

/-- **Stacks 0ED5.** Let `T` be an object of the big fppf site over `S` whose underlying
scheme is locally Noetherian and universally catenary, let `δ` be a dimension function on that
scheme, let `X` be a decent algebraic space over `S` and let `g : X ⟶ h_T` be locally of
finite type. Then the function of Stacks 0EDN induced by `δ` and `g` — the value of `δ` at the
image of a point plus the relative transcendence degree there — is a dimension function on the
points of `X`.

The hypothesis `h02JW` is Morphisms, Lemma 02JW for the base scheme and `δ`: every scheme
locally of finite type over it carries the corresponding dimension function. It belongs to
Chapter 29 and is carried here rather than proved, which is why this declaration takes no
`@[stacks]` attribute. The hypotheses `IsLocallyNoetherian` and
`AlgebraicGeometry.Scheme.IsUniversallyCatenary` are the source's and are retained so that
`h02JW` is dischargeable from Stacks 02JW; the proof below uses neither.

The proof fixes a surjective étale chart `φ : h_U ⟶ X`, factors `φ ≫ g` through the site by
full faithfulness of `CategoryTheory.yoneda`, applies `h02JW` to the resulting scheme
morphism, identifies its function with the induced function pulled back to `|U|` by
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_pointsMap_iff` and
`AlgebraicGeometry.Space.inducedDimensionValue_eq`, and then descends along the chart with
`TopologicalSpace.exists_dimensionFunction_of_generalizingMap`, whose generalizing hypothesis
is Stacks 03IL and whose surjectivity is Stacks 03H5. -/
theorem exists_dimensionFunction_inducedDimensionValue_of_isDecentSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (_hTcat : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj T))
    (δ : DimensionFunction ((BigFppfOver.toScheme B S hS).obj T))
    (h02JW : ∀ (W : Scheme.{u}) (q : W ⟶ (BigFppfOver.toScheme B S hS).obj T),
      LocallyOfFiniteType q →
        ∃ d : DimensionFunction W, ∀ w : W,
          letI := (q.residueFieldMap w).hom.toAlgebra
          d w = δ (q w) + (Cardinal.toNat (Algebra.trdeg
            (((BigFppfOver.toScheme B S hS).obj T).residueField (q w))
            (W.residueField w)) : ℤ))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (g : X ⟶ yoneda.obj T)
    (hg : IsLocallyOfFiniteType B S hS g) :
    ∃ d : DimensionFunction (points B S hS X), ∀ x : points B S hS X,
      d x = inducedDimensionValue B S hS
        (fun y ↦ δ (pointsEquivScheme B S hS T y)) g x := by
  obtain ⟨U, φ, hφSurj, hφEtale⟩ := hX.exists_atlas
  obtain ⟨τ, hmapT⟩ : ∃ τ : U ⟶ T, yoneda.map τ = φ ≫ g :=
    ⟨CategoryTheory.Yoneda.fullyFaithful.preimage (φ ≫ g),
      CategoryTheory.Yoneda.fullyFaithful.map_preimage (φ ≫ g)⟩
  have hIdEtale := (isMultiplicative_presheaf_etale B S hS).id_mem (yoneda.obj T)
  have hcomm : yoneda.map τ ≫ 𝟙 (yoneda.obj T) = φ ≫ g := by rw [Category.comp_id, hmapT]
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map τ) :=
    hg U T φ (𝟙 (yoneda.obj T)) τ hφEtale hIdEtale hcomm
  obtain ⟨d, hd⟩ :=
    h02JW ((BigFppfOver.toScheme B S hS).obj U) ((BigFppfOver.toScheme B S hS).map τ) hlft
  have hsurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U φ).mp hφSurj
  refine exists_dimensionFunction_of_generalizingMap
    ((continuous_pointsMap B S hS φ).comp (schemePointsHomeomorph B S hS U).symm.continuous)
    (hsurjPts.comp (schemePointsHomeomorph B S hS U).symm.surjective)
    (((schemePointsHomeomorph B S hS U).symm.isOpenEmbedding.generalizingMap).comp
      (generalizingMap_pointsMap_of_isDecentSpace B S hS X hX hXdec U φ hφEtale)) _ d ?_
  intro w
  let _ : Algebra (((BigFppfOver.toScheme B S hS).obj T).residueField
      ((BigFppfOver.toScheme B S hS).map τ w))
      (((BigFppfOver.toScheme B S hS).obj U).residueField w) :=
    (((BigFppfOver.toScheme B S hS).map τ).residueFieldMap w).hom.toAlgebra
  have hr := (hasTranscendenceDegreeAt_pointsMap_iff B S hS
    (Cardinal.toENat (Algebra.trdeg
      (((BigFppfOver.toScheme B S hS).obj T).residueField
        ((BigFppfOver.toScheme B S hS).map τ w))
      (((BigFppfOver.toScheme B S hS).obj U).residueField w)))
    g U T φ (𝟙 (yoneda.obj T)) τ hφEtale hIdEtale hcomm w).mpr rfl
  have hval := inducedDimensionValue_eq B S hS hX
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
    (fun y ↦ δ (pointsEquivScheme B S hS T y)) g hg _ _ hr
  have himg : pointsEquivScheme B S hS T (pointsMap B S hS X g
      (pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm w))) =
      (BigFppfOver.toScheme B S hS).map τ w := by
    rw [← pointsMap_comp_apply, ← hmapT, pointsEquivScheme_pointsMap_yoneda,
      Equiv.apply_symm_apply]
  change _ = inducedDimensionValue B S hS _ g
    (pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm w))
  rw [hd w, hval, himg, Cardinal.toNat_toENat]

end AlgebraicGeometry.Space

end
