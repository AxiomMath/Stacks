module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Supports finite over the base are the supports proper over the base

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally quasi-finite as a morphism
of schemes, and let `V` be an object of the small étale site of `Y`. The supports the
finite-support direct image is built from are the locally closed subsets of `X_V = V ×_Y X`
which carry a subscheme structure finite over `V`. Because `f` is locally quasi-finite, so is
the structure morphism `X_V ⟶ V` and so is every immersion into `X_V` followed by it; Zariski's
main theorem then says that such a morphism is finite exactly when it is proper. So the
eligible supports may equally be described by properness over `V`, which is the footnote of
the source's section on sections with finite support.

## Main results

* `AlgebraicGeometry.SmallEtale.locallyQuasiFinite_baseChangeProjection` — the structure
  morphism `X_V ⟶ V` of a base change of a locally quasi-finite morphism is locally quasi-finite.
* `AlgebraicGeometry.SmallEtale.locallyQuasiFinite_immersion_comp_baseChangeProjection` — an
  immersion into `X_V` followed by that structure morphism is locally quasi-finite.
* `AlgebraicGeometry.SmallEtale.isProper_of_isFiniteSupport` and
  `AlgebraicGeometry.SmallEtale.isFiniteSupport_of_exists_isProper` — the two halves, and
* `AlgebraicGeometry.SmallEtale.isFiniteSupport_iff_exists_isProper` — the footnote itself: a
  subset of `X_V` is an eligible support precisely when it is the range of an immersion whose
  composite with the structure morphism is proper.

## Implementation notes

The substantive half is the passage from proper to finite, and it is Zariski's main theorem in
Mathlib's form `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`. What this file
supplies is the local quasi-finiteness that theorem consumes, and that is where the local
quasi-finiteness of `f` is used: it passes to the base change `X_V ⟶ V` because local
quasi-finiteness is stable under base change and the inclusion of the big étale site into
schemes preserves pullbacks, and it then composes with an immersion because an immersion is
locally quasi-finite. The reverse half needs nothing beyond Mathlib's instance making a finite
morphism proper.

The other direction of the footnote's equivalence is therefore available for *any* morphism of
the site, while the direction producing finiteness is exactly where the source's local
quasi-finiteness enters; the equivalence is stated with that condition, as in the source.

Only the subset is recorded in `AlgebraicGeometry.SmallEtale.IsFiniteSupport`, not a chosen
subscheme structure, so both sides of the equivalence are existential over the subscheme and
the immersion, and the equivalence is a statement about subsets of `X_V`.

## References

* [Stacks Project, Tag 0F6E](https://stacks.math.columbia.edu/tag/0F6E)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The structure morphism `X_V = V ×_Y X ⟶ V` of a base change of a locally quasi-finite
morphism is locally quasi-finite. -/
public theorem locallyQuasiFinite_baseChangeProjection
    [LocallyQuasiFinite (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property) :
    LocallyQuasiFinite (B.inclusion.map (pullback.fst V.obj.hom f)) := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback V.obj.hom f).flip.map B.inclusion) inferInstance

/-- An immersion into `X_V` followed by the structure morphism `X_V ⟶ V` is locally
quasi-finite, `f` being locally quasi-finite. -/
public theorem locallyQuasiFinite_immersion_comp_baseChangeProjection
    [LocallyQuasiFinite (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property)
    {Z : Scheme.{u}} (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))
    (hi : IsImmersion i) :
    LocallyQuasiFinite (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := by
  have : IsImmersion i := hi
  exact MorphismProperty.comp_mem _ _ _ inferInstance
    (locallyQuasiFinite_baseChangeProjection B f V)

/-- An eligible support carries a subscheme structure proper over `V`: a finite morphism is
proper. -/
public theorem isProper_of_isFiniteSupport (V : SmallEtale B Y.obj Y.property)
    {E : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))}
    (hE : IsFiniteSupport B f V E) :
    ∃ (Z : Scheme.{u})
      (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)),
      IsImmersion i ∧
        IsProper (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) ∧
        Set.range i.base = E := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ := hE
  have : IsFinite (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := hfin
  exact ⟨Z, i, hi, inferInstance, hrange⟩

/-- A subset of `X_V` which is the range of an immersion proper over `V` is an eligible
support: a proper locally quasi-finite morphism is finite, which is Zariski's main theorem. -/
public theorem isFiniteSupport_of_exists_isProper
    [LocallyQuasiFinite (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property)
    {E : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))}
    (hE : ∃ (Z : Scheme.{u})
      (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)),
      IsImmersion i ∧
        IsProper (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) ∧
        Set.range i.base = E) :
    IsFiniteSupport B f V E := by
  obtain ⟨Z, i, hi, hproper, hrange⟩ := hE
  have : LocallyQuasiFinite (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) :=
    locallyQuasiFinite_immersion_comp_baseChangeProjection B f V i hi
  have : IsProper (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := hproper
  exact ⟨Z, i, hi, IsFinite.of_isProper_of_locallyQuasiFinite _, hrange⟩

/-- **Stacks 0F6E, the footnote.** For a locally quasi-finite `f`, a subset of `X_V` is an
eligible support of the finite-support direct image — the range of an immersion finite over
`V` — exactly when it is the range of an immersion *proper* over `V`. The source states this as
"since `f` is locally quasi-finite, `Z → V` is finite if and only if it is proper". -/
@[stacks 0F6E "the footnote: a support is finite over the base exactly when it is proper"]
public theorem isFiniteSupport_iff_exists_isProper
    [LocallyQuasiFinite (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property)
    (E : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))) :
    IsFiniteSupport B f V E ↔
      ∃ (Z : Scheme.{u})
        (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)),
        IsImmersion i ∧
          IsProper (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) ∧
          Set.range i.base = E :=
  ⟨isProper_of_isFiniteSupport B f V, isFiniteSupport_of_exists_isProper B f V⟩

/-! ### The rest of the section

The remaining assertions of the source's section on sections with finite support are already
formalized, and are registered against the section's tag here rather than by editing the module
which defines them. -/

add_to_stacks 0F6E "the eligible supports, locally closed and finite over the base"
  AlgebraicGeometry.SmallEtale.FiniteSupport

add_to_stacks 0F6E "closedness of one eligible support in another"
  AlgebraicGeometry.SmallEtale.finiteSupport_closedWithin

add_to_stacks 0F6E "the group of finite-support sections, as a colimit of supported sections"
  AlgebraicGeometry.SmallEtale.finiteSupportSections

add_to_stacks 0F6E "a finite-support section as a finite formal sum of supported sections"
  AlgebraicGeometry.SmallEtale.exists_finiteSupport_sum

add_to_stacks 0F6E "the restriction maps, assembling the groups into a presheaf"
  AlgebraicGeometry.SmallEtale.finiteSupportPresheaf

add_to_stacks 0F6E "the finite-support direct image presheaf as a functor"
  AlgebraicGeometry.SmallEtale.finiteSupportPushforward

end AlgebraicGeometry.SmallEtale

end
