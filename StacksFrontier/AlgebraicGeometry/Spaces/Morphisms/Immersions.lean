module

public import Mathlib.Topology.LocallyClosed
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Permanence and factorisation of immersions of algebraic spaces

This file collects the two structural facts about immersions of algebraic spaces over a scheme
`S` which the base-change criteria of
`StacksFrontier/AlgebraicGeometry/Spaces/Immersions.lean` do not address.

The first is permanence. For morphisms `Z ⟶ Y ⟶ X`, each of the properties of `Z ⟶ X` which a
monomorphism-like condition on `Y ⟶ X` makes cancellable passes to `Z ⟶ Y`: representability,
separatedness, monomorphy, being an immersion when `Y ⟶ X` is locally separated, and being a
closed immersion when `Y ⟶ X` is separated.

The second is factorisation. The image of an immersion `i : Z ⟶ X` on points is locally
closed, so its boundary is closed; the *boundary subspace* `∂Z` is the reduced closed subspace
of `X` on that boundary, and `i` factors as a closed immersion into the open subspace
complementary to `∂Z`, followed by the open immersion of that subspace into `X`. The same
construction supplies, for an arbitrary locally closed set of points, the reduced induced
subspace structure on it.

## Main definitions

* `AlgebraicGeometry.Space.boundaryComplement` is the open subspace of `X` whose point set is
  the complement of the boundary of a given set of points, that is, Mathlib's `coborder`.
* `AlgebraicGeometry.Space.reducedInducedSubspace` is the reduced induced subspace structure
  on a locally closed set of points, a closed subspace of the boundary complement.
* `AlgebraicGeometry.Space.boundarySubspace` is the boundary subspace `∂Z` of an immersion.

## Main results

* `CategoryTheory.IsPullback.of_isPullback_diag`: a base change of `g` along `t` is cut out
  of a base change of `g ≫ f` along `t ≫ f` by the diagonal of the common target of `g`
  and `t`, and `CategoryTheory.Limits.pullback.diagonal_comp_isPullback`: the relative
  diagonal of `g` is a base change of the relative diagonal of `g ≫ f`.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_comp`: if a composite is
  representable and the intermediate presheaf has representable diagonal, then the first
  factor is representable.
* `AlgebraicGeometry.Space.isSeparated_of_comp`: if a composite is separated, so is its
  first factor.
* `AlgebraicGeometry.Space.mono_of_comp`: if a composite is a monomorphism, so is its first
  factor.
* `AlgebraicGeometry.Space.isImmersion_of_comp_of_isLocallySeparated`: if a composite is an
  immersion and the second factor is locally separated, the first factor is an immersion.
* `AlgebraicGeometry.Space.isClosedImmersion_of_comp_of_isSeparated`: if a composite is a
  closed immersion and the second factor is separated, the first factor is a closed
  immersion.
* `AlgebraicGeometry.Space.isOpenSubspace_boundaryComplement` and
  `AlgebraicGeometry.Space.range_pointsMap_ι_boundaryComplement`: the complement of the
  boundary of a locally closed set of points is an open subspace with that complement as its
  point set. This is the open subspace of Stacks 06EC.
* `AlgebraicGeometry.Space.reducedInducedSubspace` is the reduced induced subspace structure
  `Z` on a locally closed set `T` of points, and
  `AlgebraicGeometry.Space.isClosedSubspace_reducedInducedSubspace`,
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedInducedSubspace`,
  `AlgebraicGeometry.Space.range_pointsMap_comp_ι_reducedInducedSubspace` and
  `AlgebraicGeometry.Space.isImmersion_comp_ι_reducedInducedSubspace` say that `Z` is a
  reduced closed subspace of `U` whose composite `Z ⟶ U ⟶ X` is an immersion with point set
  `T`. `AlgebraicGeometry.Space.eq_reducedInducedSubspace` is uniqueness and
  `AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace_of_isLocallyClosed` collects
  the two. This is Stacks 06EC.
* `AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace` and
  `AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace_boundaryComplement`: the same
  existence and uniqueness at an unnecessary descent hypothesis, the first for an arbitrary
  open subspace whose point set is the coborder of `T`.
* `AlgebraicGeometry.Space.range_pointsMap_ι_boundarySubspace` and
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_boundarySubspace`: the boundary
  subspace of an immersion has the boundary of the image as point set, and is reduced.
* `AlgebraicGeometry.Space.isClosed_range_pointsMap_of_comp_ι_boundaryComplement` and
  `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_ι_boundaryComplement`: the image of
  an immersion is closed away from its boundary, and the immersion therefore factors as a
  closed immersion followed by an open immersion.

## What is assumed

Nothing. That the reduced closed subspace on a closed set of points is a *closed subspace* is
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace` of
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean`, whose hypothesis of
effective descent along the surjective étale morphisms of the site is discharged outright by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`; a closed
immersion is affine, and closed immersions descend along fppf coverings. So every statement
of Stacks 06EC, of Stacks 04CE and of the closed-then-open factorisation of an immersion is
unconditional here.

The two declarations `AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace` and
`AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace_boundaryComplement` do take
effective descent at the immersions as a hypothesis, which they pass to
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace_of_immersionDescent`. They are
retained for consumers which already carry it; the hypothesis-free forms are the ones to use,
and they are the ones which carry `@[stacks 06EC]`.

## Implementation notes

The two immersion statements are formal: each of the three immersion properties is
`CategoryTheory.MorphismProperty.presheaf` applied to a property of morphisms of schemes
which is multiplicative and stable under base change, so the presheaf property is
multiplicative and stable under base change as well, and
`CategoryTheory.MorphismProperty.hasOfPostcompProperty_iff_le_diagonal` turns the
cancellation statement into the tautology that the diagonal condition on `Y ⟶ X` — which is
exactly local separatedness, respectively separatedness, by the definitions of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms.lean` — implies itself.

Separatedness of the first factor of a separated composite is the same argument one level
down, applied to the Cartesian square which exhibits the relative diagonal of `g` as a base
change of the relative diagonal of `g ≫ f`. It is the closed-immersion counterpart of
`AlgebraicGeometry.Space.isLocallySeparated_of_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/LocallySeparated.lean`, and is recorded
against Stacks 03KR as well as against the tag of this file.

Representability is not formal and is the source's argument: a representable base change of
`g` along a section `ξ` of `Y` is obtained from the representable base change of `g ≫ f`
along `ξ ≫ f` by a further base change along the diagonal of `Y`, which is representable
because `Y` is an algebraic space. The categorical content of that composite base change is
isolated as `CategoryTheory.IsPullback.of_isPullback_diag`, which needs neither algebraicity
nor the Yoneda embedding.

Monomorphy of the first factor is `AlgebraicGeometry.Space.mono_of_comp`, the cancellation of
monomorphisms in the presheaf category, which is Mathlib's `CategoryTheory.mono_of_mono`; it is
stated here for morphisms of algebraic spaces over `S` so that every clause of part (1) proved
in this file carries the tag on a statement about them.

The remaining two conclusions of part (1) of the source statement, local finite type and local
quasi-finiteness, are not restated here, because the statements they would restate already
exist at exactly the shape of the clause — for morphisms of algebraic spaces over `S`, with the
composite hypothesis and the first-factor conclusion — as
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeProperties.lean`, which is Stacks 0462, and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/QuasiFinite.lean`, which is
Stacks 03XN. Those two declarations carry the two clauses of this tag themselves, where they
live.

As in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms.lean`, every statement is given for an
arbitrary morphism of presheaves on the big fppf site of `S`, the algebraicity of the
intermediate object entering only through the representability of its diagonal; for morphisms
of algebraic spaces these are the source statements.

The open subspace complementary to a boundary is not a new construction: it is
`AlgebraicGeometry.Space.openSubspaceOfPoints` of Stacks 03BZ at Mathlib's `coborder`, whose
point set is already known, so `AlgebraicGeometry.Space.boundaryComplement` is a name for an
instance of an existing definition rather than a second construction of it. Likewise the
boundary subspace is `AlgebraicGeometry.Space.reducedClosedSubspace` at the boundary of the
image, which is closed precisely because `coborder` of a locally closed set is open.

The factorisation is the source's: the point set of the complement of the boundary contains the
image of the immersion, so the immersion factors through that open subspace by Stacks 03IE; the
lift is an immersion because the inclusion of an open subspace is a monomorphism, hence the
commuting triangle is Cartesian; and the lift has closed image, because its image is the
preimage, under a continuous map, of the closure of the image of the immersion. Stacks 04CD
then upgrades the lift from an immersion with closed image to a closed immersion.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 06EC](https://stacks.math.columbia.edu/tag/06EC)
* [Stacks Project, Tag 0AGC](https://stacks.math.columbia.edu/tag/0AGC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-- **A base change of a morphism `g` along `t` is cut out of a base change of `g ≫ f` along
`t ≫ f` by the diagonal of the common target of `g` and `t`.**

Given a Cartesian square exhibiting `V` as a fibre product of `g ≫ f` and `t ≫ f`, the pair
of its projections composed with `g` and with `t` is a morphism `q : V ⟶ Y ⨯ Y`; a fibre
product of `q` with the diagonal of `Y` is then a fibre product of `g` and `t`. -/
theorem IsPullback.of_isPullback_diag {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {Z Y X T V W : C} (g : Z ⟶ Y) (f : Y ⟶ X) (t : T ⟶ Y) (pZ : V ⟶ Z) (pT : V ⟶ T)
    (hp : IsPullback pZ pT (g ≫ f) (t ≫ f)) (q : V ⟶ Y ⨯ Y) (wY : W ⟶ Y) (wV : W ⟶ V)
    (hd : IsPullback wY wV (diag Y) q)
    (hq₁ : q ≫ prod.fst = pZ ≫ g) (hq₂ : q ≫ prod.snd = pT ≫ t) :
    IsPullback (wV ≫ pZ) (wV ≫ pT) g t := by
  have e₁ : wY = (wV ≫ pZ) ≫ g := by
    simpa [Category.assoc, hq₁] using congrArg (· ≫ prod.fst) hd.w
  have e₂ : wY = (wV ≫ pT) ≫ t := by
    simpa [Category.assoc, hq₂] using congrArg (· ≫ prod.snd) hd.w
  let lift : ∀ s : PullbackCone g t, s.pt ⟶ W := fun s ↦ by
    refine hd.lift (s.fst ≫ g)
      (hp.lift s.fst s.snd
        (by simpa only [Category.assoc] using congrArg (· ≫ f) s.condition)) ?_
    apply prod.hom_ext
    · simp [Category.assoc, hq₁]
    · simpa [Category.assoc, hq₂, hp.lift_snd] using s.condition
  refine ⟨⟨e₁.symm.trans e₂⟩,
    ⟨PullbackCone.IsLimit.mk (f := g) (g := t) (e₁.symm.trans e₂) lift ?_ ?_ ?_⟩⟩
  · exact fun s ↦ by simp [lift, hp.lift_fst]
  · exact fun s ↦ by simp [lift, hp.lift_snd]
  · intro s m hm₁ hm₂
    have hmV : m ≫ wV =
        hp.lift s.fst s.snd
          (by simpa only [Category.assoc] using congrArg (· ≫ f) s.condition) :=
      hp.hom_ext (by simpa [Category.assoc] using hm₁) (by simpa [Category.assoc] using hm₂)
    refine hd.hom_ext ?_ ?_
    · calc m ≫ wY = s.fst ≫ g := by
            simpa only [e₁, Category.assoc] using congrArg (· ≫ g) hm₁
        _ = lift s ≫ wY := by dsimp [lift]; simp [hd.lift_fst]
    · dsimp [lift]
      simp only [hd.lift_snd]
      exact hmV

/-- **The relative diagonal of a composite `g ≫ f` base-changes to the relative diagonal of
`g`.** The base change is along `CategoryTheory.Limits.pullback.mapDesc`, the comparison map
of the two fibre products of the source with itself. -/
theorem Limits.pullback.diagonal_comp_isPullback {C : Type u} [Category.{v} C] [HasPullbacks C]
    {Z Y X : C} (g : Z ⟶ Y) (f : Y ⟶ X) :
    IsPullback (𝟙 Z) (pullback.diagonal g) (pullback.diagonal (g ≫ f))
      (pullback.mapDesc g g f) := by
  have hmfst : pullback.mapDesc g g f ≫ pullback.fst (g ≫ f) (g ≫ f) = pullback.fst g g := by
    simp only [pullback.mapDesc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hmsnd : pullback.mapDesc g g f ≫ pullback.snd (g ≫ f) (g ≫ f) = pullback.snd g g := by
    simp only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.mk' ?_ (fun _ _ _ h₁ _ ↦ by simpa using h₁) ?_
  · apply pullback.hom_ext <;>
      simp [pullback.diagonal_fst, pullback.diagonal_snd, Category.assoc, hmfst, hmsnd]
  · intro T a b h
    refine ⟨a, by simp, ?_⟩
    have hfst : a = b ≫ pullback.fst g g := by
      simpa [hmfst] using congrArg (· ≫ pullback.fst (g ≫ f) (g ≫ f)) h
    have hsnd : a = b ≫ pullback.snd g g := by
      simpa [hmsnd] using congrArg (· ≫ pullback.snd (g ≫ f) (g ≫ f)) h
    apply pullback.hom_ext
    · simpa [Category.assoc, pullback.diagonal_fst] using hfst
    · simpa [Category.assoc, pullback.diagonal_snd] using hsnd

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site times out;
supply them directly. -/
local instance (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) hasLimit_cospan_presheaf_Immersions
    {Z₁ Z₂ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z₀) (f : Z₂ ⟶ Z₀) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _


/-! ### Representability -/

/-- **Stacks 0AGC, part (1): representability.** If a composite of morphisms of presheaves on
the big fppf site of `S` is representable and the intermediate presheaf has representable
diagonal — in particular, if it is an algebraic space over `S` — then the first factor is
representable. -/
@[stacks 0AGC "part (1): representable"]
theorem relativelyRepresentable_of_comp (hY : yoneda.relativelyRepresentable (diag Y))
    (g : Z ⟶ Y) (f : Y ⟶ X) (hgf : yoneda.relativelyRepresentable (g ≫ f)) :
    yoneda.relativelyRepresentable g := by
  refine (yoneda_relativelyRepresentable_iff_pullback_representable g).2 fun T ξ ↦ ?_
  set y := yonedaEquiv.symm ξ with hy
  obtain ⟨V, vT, vZ, hp⟩ := hgf (y ≫ f)
  obtain ⟨W, wV, wY, hd⟩ := hY (prod.lift (vZ ≫ g) (yoneda.map vT ≫ y))
  refine Functor.IsRepresentable.mk' (X := W) ?_
  have hpb : IsPullback (yoneda.map wV ≫ vZ) (yoneda.map wV ≫ yoneda.map vT) g y := by
    simpa using IsPullback.of_isPullback_diag g f y vZ (yoneda.map vT) hp _ wY
      (yoneda.map wV) hd (by simp) (by simp)
  simpa using hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback y g)

/-! ### Separatedness -/

/-- **Stacks 0AGC, part (1): separatedness.** If a composite of morphisms of algebraic spaces
over `S` is separated, so is its first factor.

This is also the separated part of **Stacks 03KR**, whose locally separated and
quasi-separated parts are `AlgebraicGeometry.Space.isLocallySeparated_of_comp` and
`AlgebraicGeometry.Space.isQuasiSeparated_of_comp`. -/
@[stacks 0AGC "part (1): separated", ega "I 5.5.1" "(v)"]
theorem isSeparated_of_comp (g : Z ⟶ Y) (f : Y ⟶ X)
    (hgf : IsSeparated B S hS (g ≫ f)) :
    IsSeparated B S hS g := by
  let P : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have _ : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  change IsClosedImmersion B S hS (pullback.diagonal (g ≫ f)) at hgf
  change IsClosedImmersion B S hS (pullback.diagonal g)
  exact MorphismProperty.of_isPullback (pullback.diagonal_comp_isPullback g f) hgf

/-! ### Monomorphisms -/

/-- **Stacks 0AGC, part (1): monomorphisms.** If a composite of morphisms of algebraic spaces
over `S` is a monomorphism, so is its first factor.

Monomorphy of a morphism of algebraic spaces over `S` is monomorphy of the underlying morphism
of presheaves on the big fppf site of `S`, by `AlgebraicGeometry.Space.mono_hom_iff_mono` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Monomorphisms.lean`, so this clause is the
cancellation of monomorphisms `CategoryTheory.mono_of_mono` read in that presheaf category.
Nothing is required of `Y`. -/
@[stacks 0AGC "part (1): monomorphism"]
theorem mono_of_comp (g : Z ⟶ Y) (f : Y ⟶ X) (hgf : Mono (g ≫ f)) : Mono g :=
  have := hgf
  mono_of_mono g f

/-! ### Immersions and closed immersions -/

/-- For a multiplicative property `R` of schemes stable under base change, the property of
morphisms of presheaves induced by `R` can be cancelled against a second factor whose diagonal
has it. -/
private theorem hasOfPostcompProperty_inverseImage_toScheme (R : MorphismProperty Scheme.{u})
    [R.IsMultiplicative] [R.IsStableUnderBaseChange] :
    (R.inverseImage (BigFppfOver.toScheme B S hS)).presheaf.HasOfPostcompProperty
      (R.inverseImage (BigFppfOver.toScheme B S hS)).presheaf.diagonal := by
  have _ : R.ContainsIdentities := (inferInstance : R.IsMultiplicative).toContainsIdentities
  have _ : R.IsStableUnderComposition := ⟨(inferInstance : R.IsMultiplicative).comp_mem⟩
  have _ : R.RespectsIso := (inferInstance : R.IsStableUnderBaseChange).respectsIso
  let Q : MorphismProperty (BigFppfOver B S hS) := R.inverseImage (BigFppfOver.toScheme B S hS)
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have _ : Q.ContainsIdentities := MorphismProperty.ContainsIdentities.inverseImage _
  have _ : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : Q.IsMultiplicative := MorphismProperty.IsMultiplicative.mk
  have _ : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  have _ : Q.presheaf.IsMultiplicative := MorphismProperty.relative_isMultiplicative Q
  exact (MorphismProperty.hasOfPostcompProperty_iff_le_diagonal
    (P := Q.presheaf) (Q := Q.presheaf.diagonal)).2 le_rfl

/-- **Stacks 0AGC, part (2).** If a composite of morphisms of algebraic spaces over `S` is an
immersion and its second factor is locally separated, then its first factor is an
immersion. -/
@[stacks 0AGC "part (2): immersion"]
theorem isImmersion_of_comp_of_isLocallySeparated (g : Z ⟶ Y) (f : Y ⟶ X)
    (hgf : IsImmersion B S hS (g ≫ f)) (hf : IsLocallySeparated B S hS f) :
    IsImmersion B S hS g :=
  (hasOfPostcompProperty_inverseImage_toScheme B S hS
    (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})).of_postcomp
      g f hf hgf

/-- **Stacks 0AGC, part (3).** If a composite of morphisms of algebraic spaces over `S` is a
closed immersion and its second factor is separated, then its first factor is a closed
immersion. -/
@[stacks 0AGC "part (3): closed immersion", ega "I 5.4.4"]
theorem isClosedImmersion_of_comp_of_isSeparated (g : Z ⟶ Y) (f : Y ⟶ X)
    (hgf : IsClosedImmersion B S hS (g ≫ f)) (hf : IsSeparated B S hS f) :
    IsClosedImmersion B S hS g :=
  (hasOfPostcompProperty_inverseImage_toScheme B S hS
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})).of_postcomp
      g f hf hgf

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site times out;
supply them directly. -/
local instance (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) hasLimit_cospan_presheaf_aux_Immersions
    {Z₁ Z₂ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z₀) (f : Z₂ ⟶ Z₀) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _


/-! ### The complement of the boundary of a locally closed set of points -/

/-- **Stacks 06EC, the open subspace.** The open subspace of `X` obtained by removing the
boundary `closure T \ T` of a set `T` of points of `X`: its point set is Mathlib's
`coborder T`.

This is `AlgebraicGeometry.Space.openSubspaceOfPoints` at `coborder T`; the definition needs
no hypothesis on `T`, local closedness entering only through
`AlgebraicGeometry.Space.isOpenSubspace_boundaryComplement`. -/
@[stacks 06EC "the open subspace U with |U| = |X| ∖ ∂T"]
noncomputable def boundaryComplement (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) : Subfunctor X :=
  openSubspaceOfPoints B S hS X (coborder T)

/-- **The point set of the complement of the boundary of `T` is `coborder T`**, that is, the
complement of `closure T \ T`. This is the defining property `|U| = |X| ∖ ∂T` of the open
subspace `U` of Stacks 06EC. -/
@[stacks 06EC "the point set of U is the complement of the boundary of T"]
theorem range_pointsMap_ι_boundaryComplement (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) :
    Set.range (pointsMap B S hS (boundaryComplement B S hS X T).toFunctor
      (boundaryComplement B S hS X T).ι) = coborder T :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS (coborder T)

/-- **The complement of the boundary of a locally closed set of points of an algebraic space is
an open subspace of it.** This is the open subspace `U` of Stacks 06EC, whose existence the
source takes from Stacks 03BZ. -/
@[stacks 06EC "U is an open subspace of X"]
theorem isOpenSubspace_boundaryComplement (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    IsOpenSubspace B S hS (boundaryComplement B S hS X T) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _ hT.isOpen_coborder

/-- A locally closed set of points is contained in the point set of the complement of its
boundary. -/
theorem range_pointsMap_ι_boundaryComplement_superset
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : Set (points B S hS X)) :
    T ⊆ Set.range (pointsMap B S hS (boundaryComplement B S hS X T).toFunctor
      (boundaryComplement B S hS X T).ι) :=
  (range_pointsMap_ι_boundaryComplement B S hS X T).symm ▸ subset_coborder

/-! ### The reduced induced subspace on a locally closed set of points

What follows is the content of Stacks 06EC past the open subspace: a locally closed set `T` of
points of `X` is closed in the complement `U` of its boundary, so it carries there the reduced
induced closed subspace structure of Stacks 03IQ, and the composite of that closed immersion
with the open immersion `U ⟶ X` is an immersion with point set `T`.

Every clause is unconditional. That the subspace is a *closed* subspace is
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`, whose own hypothesis of
effective descent along the surjective étale morphisms of the site is discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`: the
construction descends an ideal along a chart, so what it needs is effective descent at the
*closed immersions*, and that holds outright. The unconditional statements are
`AlgebraicGeometry.Space.reducedInducedSubspace` and the lemmas named after it, and they are
what carries `@[stacks 06EC]`.

The two statements immediately below instead take effective descent at the immersions as a
hypothesis, which they pass to
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace_of_immersionDescent`. They are
the general-`U` form, for a consumer with an open subspace not presented as a boundary
complement, and its specialisation to the boundary complement. -/

/-- The preimage of `T` in an open subspace whose point set is `coborder T` is closed. -/
private theorem isClosed_preimage_of_range_eq_coborder {U : Subfunctor X}
    {T : Set (points B S hS X)}
    (hUT : Set.range (pointsMap B S hS U.toFunctor U.ι) = coborder T) :
    IsClosed (pointsMap B S hS U.toFunctor U.ι ⁻¹' T) := by
  have hpre : pointsMap B S hS U.toFunctor U.ι ⁻¹' coborder T = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun x ↦ hUT ▸ Set.mem_range_self x
  rw [show pointsMap B S hS U.toFunctor U.ι ⁻¹' T =
      pointsMap B S hS U.toFunctor U.ι ⁻¹' (closure T ∩ coborder T) by
    rw [closure_inter_coborder], Set.preimage_inter, hpre, Set.inter_univ]
  exact isClosed_closure.preimage (continuous_pointsMap B S hS U.ι)

/-- The image of the preimage of `T` in an open subspace whose point set is `coborder T` is
`T`. -/
private theorem image_preimage_of_range_eq_coborder {U : Subfunctor X}
    {T : Set (points B S hS X)}
    (hUT : Set.range (pointsMap B S hS U.toFunctor U.ι) = coborder T) :
    pointsMap B S hS U.toFunctor U.ι '' (pointsMap B S hS U.toFunctor U.ι ⁻¹' T) = T :=
  Set.image_preimage_eq_of_subset (hUT.symm ▸ subset_coborder)

/-- The point set of a subspace of `U` seen in `|X|` is the image of its point set in `|U|`. -/
private theorem range_pointsMap_comp_ι_eq_image {U : Subfunctor X}
    (W : Subfunctor U.toFunctor) :
    Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ U.ι)) =
      pointsMap B S hS U.toFunctor U.ι '' Set.range (pointsMap B S hS W.toFunctor W.ι) := by
  rw [pointsMap_comp, Set.range_comp]

/-- **The reduced induced subspace**, at a hypothesis of effective descent for immersions
along the surjective étale morphisms of the site.

A set of points of an algebraic space which is closed in the complement `U` of its boundary
carries a unique reduced closed subspace structure in `U`, whose composite with the inclusion
of `U` is an immersion onto that set of points.

The hypothesis is not needed: for the boundary complement this is
`AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace_of_isLocallyClosed`, which has
no hypothesis beyond local closedness and carries the Stacks tag. This form is stated for an
arbitrary open subspace `U` whose point set is the coborder of `T`. -/
theorem existsUnique_reducedInducedSubspace
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}))
    {U : Subfunctor X} (hU : IsOpenSubspace B S hS U) {T : Set (points B S hS X)}
    (hUT : Set.range (pointsMap B S hS U.toFunctor U.ι) = coborder T) :
    ∃! W : Subfunctor U.toFunctor,
      IsClosedSubspace B S hS W ∧
        HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y) ∧
          Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ U.ι)) = T ∧
            IsImmersion B S hS (W.ι ≫ U.ι) := by
  have himage := image_preimage_of_range_eq_coborder B S hS hUT
  have hT' := isClosed_preimage_of_range_eq_coborder B S hS hUT
  obtain ⟨W, hW, hWuniq⟩ :=
    existsUnique_reducedClosedSubspace_of_immersionDescent B S hS U.toFunctor hU.1 _ hT' hdesc
  refine ⟨W, ⟨hW.1, hW.2.2, ?_, ?_⟩, fun V hV ↦ hWuniq V ⟨hV.1, ?_, hV.2.1⟩⟩
  · rw [range_pointsMap_comp_ι_eq_image, hW.2.1, himage]
  · exact isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS hW.1.2)
      (isImmersion_of_isOpenImmersion B S hS hU.2)
  · refine (pointsMap_injective_of_mono B S hS U.ι).image_injective ?_
    rw [← range_pointsMap_comp_ι_eq_image, hV.2.2.1, himage]

/-- **The reduced induced subspace at the complement of the boundary**, at a hypothesis of
effective descent for immersions along the surjective étale morphisms of the site.

A locally closed set `T` of points of an algebraic space `X` over `S` carries a unique reduced
closed subspace structure inside the complement of its boundary, and that subspace is an
immersion into `X` with point set `T`. This is the *reduced induced subspace structure* on `T`.

The hypothesis is not needed: the same statement without it is
`AlgebraicGeometry.Space.existsUnique_reducedInducedSubspace_of_isLocallyClosed`, which
carries the Stacks tag. -/
theorem existsUnique_reducedInducedSubspace_boundaryComplement
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) {T : Set (points B S hS X)}
    (hT : IsLocallyClosed T) :
    ∃! W : Subfunctor (boundaryComplement B S hS X T).toFunctor,
      IsClosedSubspace B S hS W ∧
        HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y) ∧
          Set.range (pointsMap B S hS W.toFunctor
            (W.ι ≫ (boundaryComplement B S hS X T).ι)) = T ∧
            IsImmersion B S hS (W.ι ≫ (boundaryComplement B S hS X T).ι) :=
  existsUnique_reducedInducedSubspace B S hS hdesc
    (isOpenSubspace_boundaryComplement B S hS hX hT)
    (range_pointsMap_ι_boundaryComplement B S hS X T)

/-! ### The reduced induced subspace, unconditionally -/

/-- A set `T` of points of `X` is closed in an open subspace `U` whose point set is the
coborder of `T`: there the preimage of `T` is the preimage of `closure T`. -/
theorem isClosed_preimage_pointsMap_ι_of_range_eq_coborder {U : Subfunctor X}
    {T : Set (points B S hS X)}
    (hUT : Set.range (pointsMap B S hS U.toFunctor U.ι) = coborder T) :
    IsClosed (pointsMap B S hS U.toFunctor U.ι ⁻¹' T) :=
  isClosed_preimage_of_range_eq_coborder B S hS hUT

/-- The image in `|X|` of the preimage of `T` in such an open subspace is all of `T`. -/
theorem image_preimage_pointsMap_ι_of_range_eq_coborder {U : Subfunctor X}
    {T : Set (points B S hS X)}
    (hUT : Set.range (pointsMap B S hS U.toFunctor U.ι) = coborder T) :
    pointsMap B S hS U.toFunctor U.ι '' (pointsMap B S hS U.toFunctor U.ι ⁻¹' T) = T :=
  image_preimage_of_range_eq_coborder B S hS hUT

/-- The point set of a subspace of `U` seen in `|X|` is the image of its point set in `|U|`. -/
theorem range_pointsMap_comp_ι {U : Subfunctor X} (W : Subfunctor U.toFunctor) :
    Set.range (pointsMap B S hS W.toFunctor (W.ι ≫ U.ι)) =
      pointsMap B S hS U.toFunctor U.ι '' Set.range (pointsMap B S hS W.toFunctor W.ι) :=
  range_pointsMap_comp_ι_eq_image B S hS W

/-- **Stacks 06EC, the reduced induced subspace `Z`.** The *reduced induced subspace structure*
on a locally closed set `T` of points of an algebraic space `X` over `S`: the reduced induced
closed subspace of Stacks 03IQ on `T`, formed inside the open subspace
`AlgebraicGeometry.Space.boundaryComplement` complementary to the boundary of `T`, where `T`
is closed. -/
@[stacks 06EC "the reduced induced subspace Z on a locally closed set of points"]
noncomputable def reducedInducedSubspace (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    Subfunctor (boundaryComplement B S hS X T).toFunctor :=
  reducedClosedSubspace B S hS (boundaryComplement B S hS X T).toFunctor
    (isOpenSubspace_boundaryComplement B S hS hX hT).1
    (pointsMap B S hS (boundaryComplement B S hS X T).toFunctor
      (boundaryComplement B S hS X T).ι ⁻¹' T)
    (isClosed_preimage_pointsMap_ι_of_range_eq_coborder B S hS
      (range_pointsMap_ι_boundaryComplement B S hS X T))

/-- **Stacks 06EC.** The reduced induced subspace on `T` is a closed subspace of the open
subspace complementary to the boundary of `T`, so `Z ⟶ U` is a closed immersion. -/
@[stacks 06EC "Z is a closed subspace of U, so Z ⟶ U is a closed immersion"]
theorem isClosedSubspace_reducedInducedSubspace (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    IsClosedSubspace B S hS (reducedInducedSubspace B S hS hX hT) :=
  isClosedSubspace_reducedClosedSubspace B S hS _ _ _ _

/-- **Stacks 06EC.** The reduced induced subspace on `T` is reduced, in the étale-local sense
of Stacks 03E6. -/
@[stacks 06EC "Z is a reduced algebraic space"]
theorem hasEtaleLocalProperty_isReduced_reducedInducedSubspace
    (hX : IsAlgebraicSpace B S hS X) {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    HasEtaleLocalProperty B S hS (reducedInducedSubspace B S hS hX hT).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS _ _ _ _

/-- The point set of the reduced induced subspace on `T`, as a subset of the points of the
open subspace complementary to the boundary of `T`, is the preimage of `T` there. -/
theorem range_pointsMap_ι_reducedInducedSubspace (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    Set.range (pointsMap B S hS (reducedInducedSubspace B S hS hX hT).toFunctor
        (reducedInducedSubspace B S hS hX hT).ι) =
      pointsMap B S hS (boundaryComplement B S hS X T).toFunctor
        (boundaryComplement B S hS X T).ι ⁻¹' T :=
  range_pointsMap_ι_reducedClosedSubspace B S hS _ _ _ _

/-- **Stacks 06EC.** The point set of the reduced induced subspace on `T` is `T` itself, as a
subset of the points of `X`. -/
@[stacks 06EC "|Z| = T as subsets of |X|"]
theorem range_pointsMap_comp_ι_reducedInducedSubspace (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    Set.range (pointsMap B S hS (reducedInducedSubspace B S hS hX hT).toFunctor
      ((reducedInducedSubspace B S hS hX hT).ι ≫ (boundaryComplement B S hS X T).ι)) = T := by
  rw [range_pointsMap_comp_ι, range_pointsMap_ι_reducedInducedSubspace]
  exact image_preimage_pointsMap_ι_of_range_eq_coborder B S hS
    (range_pointsMap_ι_boundaryComplement B S hS X T)

/-- **Stacks 06EC.** The composite `Z ⟶ U ⟶ X` of the reduced induced subspace on `T` with the
open subspace complementary to the boundary of `T` is an immersion: a closed immersion
followed by an open immersion, by Stacks 02YV. -/
@[stacks 06EC "Z ⟶ U ⟶ X is an immersion"]
theorem isImmersion_comp_ι_reducedInducedSubspace (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    IsImmersion B S hS ((reducedInducedSubspace B S hS hX hT).ι ≫
      (boundaryComplement B S hS X T).ι) := by
  exact isImmersion_comp B S hS _ _
    (isImmersion_of_isClosedImmersion B S hS
      (isClosedSubspace_reducedInducedSubspace B S hS hX hT).2)
    (isImmersion_of_isOpenImmersion B S hS (isOpenSubspace_boundaryComplement B S hS hX hT).2)

/-- **Stacks 06EC, uniqueness.** A reduced closed subspace of the open subspace complementary
to the boundary of `T` whose point set in `|X|` is `T` is the reduced induced subspace on
`T`. -/
@[stacks 06EC "uniqueness of the reduced induced subspace"]
theorem eq_reducedInducedSubspace (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsLocallyClosed T)
    (W : Subfunctor (boundaryComplement B S hS X T).toFunctor)
    (hWc : IsClosedSubspace B S hS W)
    (hWT : Set.range (pointsMap B S hS W.toFunctor
      (W.ι ≫ (boundaryComplement B S hS X T).ι)) = T)
    (hWr : HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y)) :
    W = reducedInducedSubspace B S hS hX hT := by
  refine eq_reducedClosedSubspace B S hS _ _ _ _ W hWc ?_ hWr
  refine (pointsMap_injective_of_mono B S hS
    (boundaryComplement B S hS X T).ι).image_injective ?_
  rw [← range_pointsMap_comp_ι, hWT,
    image_preimage_pointsMap_ι_of_range_eq_coborder B S hS
      (range_pointsMap_ι_boundaryComplement B S hS X T)]

/-- **Stacks 06EC.** A locally closed set `T` of points of an algebraic space `X` over `S`
carries a unique reduced closed subspace structure inside the open subspace complementary to
its boundary, and that subspace is an immersion into `X` with point set `T`. This is the
*reduced induced subspace structure* on `T`, and it is
`AlgebraicGeometry.Space.reducedInducedSubspace`. -/
@[stacks 06EC "existence and uniqueness of the reduced induced subspace"]
theorem existsUnique_reducedInducedSubspace_of_isLocallyClosed
    (hX : IsAlgebraicSpace B S hS X) {T : Set (points B S hS X)} (hT : IsLocallyClosed T) :
    ∃! W : Subfunctor (boundaryComplement B S hS X T).toFunctor,
      IsClosedSubspace B S hS W ∧
        HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y) ∧
          Set.range (pointsMap B S hS W.toFunctor
            (W.ι ≫ (boundaryComplement B S hS X T).ι)) = T ∧
            IsImmersion B S hS (W.ι ≫ (boundaryComplement B S hS X T).ι) :=
  ⟨reducedInducedSubspace B S hS hX hT,
    ⟨isClosedSubspace_reducedInducedSubspace B S hS hX hT,
      hasEtaleLocalProperty_isReduced_reducedInducedSubspace B S hS hX hT,
      range_pointsMap_comp_ι_reducedInducedSubspace B S hS hX hT,
      isImmersion_comp_ι_reducedInducedSubspace B S hS hX hT⟩,
    fun W hW ↦ eq_reducedInducedSubspace B S hS hX hT W hW.1 hW.2.2.1 hW.2.1⟩

/-! ### The boundary subspace of an immersion -/

/-- **Stacks 04CE.** The boundary subspace `∂Z` of an immersion `i : Z ⟶ X` of algebraic
spaces over `S`: the reduced closed subspace of `X` supported on the boundary
`closure |Z| \ |Z|` of the image of `i` on points.

The image of an immersion is locally closed, so its boundary is closed and the reduced
induced closed subspace structure of
`AlgebraicGeometry.Space.reducedClosedSubspace` applies to it. -/
noncomputable def boundarySubspace (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) : Subfunctor X :=
  reducedClosedSubspace B S hS X hX
    (closure (Set.range (pointsMap B S hS Z i)) \ Set.range (pointsMap B S hS Z i))
    (isOpen_compl_iff.mp
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS hX i hi).isOpen_coborder)

/-- **Stacks 04CE.** The point set of the boundary subspace of an immersion is the boundary
of the image of that immersion. -/
@[stacks 04CE "the points of the boundary subspace"]
theorem range_pointsMap_ι_boundarySubspace (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) :
    Set.range (pointsMap B S hS (boundarySubspace B S hS hX i hi).toFunctor
        (boundarySubspace B S hS hX i hi).ι) =
      closure (Set.range (pointsMap B S hS Z i)) \ Set.range (pointsMap B S hS Z i) :=
  range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ _

/-- **Stacks 04CE.** The boundary subspace of an immersion is reduced, in the étale-local
sense of Stacks 03E6. -/
@[stacks 04CE "the boundary subspace is reduced"]
theorem hasEtaleLocalProperty_isReduced_boundarySubspace (hX : IsAlgebraicSpace B S hS X)
    (i : Z ⟶ X) (hi : IsImmersion B S hS i) :
    HasEtaleLocalProperty B S hS (boundarySubspace B S hS hX i hi).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _ _

/-- **Stacks 04CE.** The open subspace through which an immersion is to be factored is the
complement of its boundary subspace: the two have complementary point sets. -/
@[stacks 04CE "the open subspace is the complement of the boundary subspace"]
theorem range_pointsMap_ι_boundaryComplement_eq_compl (hX : IsAlgebraicSpace B S hS X)
    (i : Z ⟶ X) (hi : IsImmersion B S hS i) :
    Set.range (pointsMap B S hS
        (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).toFunctor
        (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).ι) =
      (Set.range (pointsMap B S hS (boundarySubspace B S hS hX i hi).toFunctor
        (boundarySubspace B S hS hX i hi).ι))ᶜ := by
  rw [range_pointsMap_ι_boundaryComplement, range_pointsMap_ι_boundarySubspace]
  rfl

/-! ### An immersion is a closed immersion into the complement of its boundary -/

/-- **A morphism into an open subspace whose point set is the coborder of the image of the
composite has closed image.** The image is the preimage, under the inclusion of the open
subspace on points, of the closure of the image of the composite; and that inclusion is
continuous. -/
theorem isClosed_range_pointsMap_of_range_eq_coborder {U : Subfunctor X}
    {T : Set (points B S hS X)}
    (hU : Set.range (pointsMap B S hS U.toFunctor U.ι) = coborder T) (g : Z ⟶ U.toFunctor)
    (hg : Set.range (pointsMap B S hS Z (g ≫ U.ι)) = T) :
    IsClosed (Set.range (pointsMap B S hS Z g)) := by
  have hcomp : ∀ z, pointsMap B S hS U.toFunctor U.ι (pointsMap B S hS Z g z) =
      pointsMap B S hS Z (g ≫ U.ι) z := fun z ↦ by rw [pointsMap_comp]; rfl
  have hRange : Set.range (pointsMap B S hS Z g) =
      pointsMap B S hS U.toFunctor U.ι ⁻¹' closure T := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro y ⟨z, rfl⟩
      refine subset_closure ?_
      rw [← hg]
      exact ⟨z, (hcomp z).symm⟩
    · intro y hy
      have hyT : pointsMap B S hS U.toFunctor U.ι y ∈
          Set.range (pointsMap B S hS Z (g ≫ U.ι)) := by
        rw [hg]
        exact mem_coborder_iff_imp.mp (hU ▸ Set.mem_range_self y) hy
      obtain ⟨z, hz⟩ := hyT
      exact ⟨z, pointsMap_injective_of_mono B S hS U.ι ((hcomp z).trans hz)⟩
  rw [hRange]
  exact isClosed_closure.preimage (continuous_pointsMap B S hS U.ι)

/-- **Stacks 04CE.** The image of an immersion is closed in the complement of its boundary:
any factorisation of the immersion through that open subspace has closed image on points. -/
@[stacks 04CE "the image is closed away from the boundary"]
theorem isClosed_range_pointsMap_of_comp_ι_boundaryComplement (i : Z ⟶ X)
    (g : Z ⟶ (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).toFunctor)
    (hg : g ≫ (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).ι = i) :
    IsClosed (Set.range (pointsMap B S hS Z g)) :=
  isClosed_range_pointsMap_of_range_eq_coborder B S hS
    (range_pointsMap_ι_boundaryComplement B S hS X _) g (by rw [hg])

/-- **Stacks 04CE.** Every immersion of algebraic spaces over `S` factors as a closed
immersion into the complement of its boundary, followed by the open immersion of that open
subspace into the target. -/
@[stacks 04CE "an immersion is a closed immersion followed by an open immersion"]
theorem exists_isClosedImmersion_comp_ι_boundaryComplement
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z) (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) :
    ∃ g : Z ⟶ (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).toFunctor,
      IsClosedImmersion B S hS g ∧
        g ≫ (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).ι = i := by
  have hU : IsOpenSubspace B S hS (boundaryComplement B S hS X
      (Set.range (pointsMap B S hS Z i))) :=
    isOpenSubspace_boundaryComplement B S hS hX
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS hX i hi)
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hZ _ hU i).2
    (range_pointsMap_ι_boundaryComplement_superset B S hS X _)
  have _ : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hgi : IsImmersion B S hS g :=
    MorphismProperty.of_isPullback
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 Z) (snd := g) (f := i)
        (g := (boundaryComplement B S hS X (Set.range (pointsMap B S hS Z i))).ι)
        ⟨by simpa using hg.symm⟩) hi
  exact ⟨g, (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hU.1 g hgi).2
    (isClosed_range_pointsMap_of_comp_ι_boundaryComplement B S hS i g hg), hg⟩

end AlgebraicGeometry.Space

end
