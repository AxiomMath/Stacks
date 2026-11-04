module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ClosedImmersionMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.FiniteMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperDescent

/-!
# The data of Situation 084W, with the limit proved to be an algebraic space

**Situation 084W** consists of a directed inverse system `(B_i)` of algebraic spaces over `S`
with affine transition morphisms, a distinguished index `0`, and a morphism `f₀ : X₀ ⟶ Y₀` of
algebraic spaces over `B₀`, with `B₀`, `X₀` and `Y₀` quasi-compact and quasi-separated. Under
the standing convention of Section 70.2 (Stacks 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, the limit `B = lim B_i` is an algebraic
space (Stacks 07SF), which already follows from the quasi-compactness of the single stage `B₀`.
In Situation 084W the morphism `f : X ⟶ Y` of limits descends to a stage with each of the
properties affine, finite, closed immersion and proper that it has, and properness of the
scheme-theoretic support of a module of finite type descends likewise.

## Main definitions

* `AlgebraicGeometry.Space.MorphismDescentData`: the data of Situation 084W.
* `AlgebraicGeometry.Space.MorphismDescentData.toMorphismDescentSituation`: the same data with
  the limit an algebraic space, under the convention.

## Main results

* `isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits_of_isQuasiCompactSpace`: under the
  convention, the limit of a cofiltered system of algebraic spaces with affine transition
  morphisms and one quasi-compact stage is an algebraic space.
* `AlgebraicGeometry.Space.MorphismDescentData.exists_isAffineHom_mapAt`: if `f` is affine, then
  some `f_i` is affine.
* `AlgebraicGeometry.Space.MorphismDescentData.exists_isFinite_mapAt`: if `f` is finite and `f₀`
  is locally of finite type, then some `f_i` is finite.
* `AlgebraicGeometry.Space.MorphismDescentData.exists_isClosedImmersion_mapAt`: if `f` is a
  closed immersion and `f₀` is locally of finite type, then some `f_i` is a closed immersion.
* `AlgebraicGeometry.Space.MorphismDescentData.exists_isProper_mapAt`: if `f` is proper and `f₀`
  is locally of finite type, then some `f_i` is proper.
* `AlgebraicGeometry.Space.MorphismDescentData.exists_isProper_schemeTheoreticSupport_moduleAt`:
  if the scheme-theoretic support of the pullback of a finite type quasi-coherent module is
  proper over `Y`, then so is that of its pullback to some stage over `Y_i`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 084Y](https://stacks.math.columbia.edu/tag/084Y)
* [Stacks Project, Tag 084Z](https://stacks.math.columbia.edu/tag/084Z)
* [Stacks Project, Tag 0850](https://stacks.math.columbia.edu/tag/0850)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Limit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 07SF, existence, under the chapter's convention, from one quasi-compact stage.**
Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms satisfying `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, and let one stage
`D i` be quasi-compact. Then `limit D` is an algebraic space. -/
theorem isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits_of_isQuasiCompactSpace
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : I) (hQc : IsQuasiCompactSpace B S hS (D.obj i)) :
    IsAlgebraicSpace B S hS (limit D) := by
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i) (hD i)).mp
      hQc
  obtain ⟨U, p, q, hp⟩ :=
    isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv hAffine i ⟨U₀, hU₀⟩ p₀
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  exact isAlgebraicSpace_of_surjective_etale_atlas B S hS
    (isSheaf_limit B S hS D fun i => (hD i).isSheaf) U.obj p
    (P.presheaf.of_isPullback hp.flip hs₀)
    (E.presheaf.of_isPullback hp.flip ((isEtale_iff_presheaf_of_yoneda B S hS p₀).mp he₀))

end Limit

/-- **The data of Situation 084W.** A directed inverse system `(B_i)` of algebraic spaces over
`S` with affine transition morphisms, a distinguished index `0 ∈ I`, and a morphism
`f₀ : X₀ ⟶ Y₀` of algebraic spaces over `B₀`, with `B₀`, `X₀` and `Y₀` quasi-compact and
quasi-separated. Unlike `AlgebraicGeometry.Space.MorphismDescentSituation` it does not ask the
limit to be an algebraic space. -/
structure MorphismDescentData (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(B_i)` of presheaves on the big fppf site over `S`. -/
  base : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Every member of the system is an algebraic space over `S`. -/
  base_isAlgebraicSpace : ∀ i : I, IsAlgebraicSpace B S hS (base.obj (op i))
  /-- Every transition morphism of the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (base.map a)
  /-- The distinguished stage `0 ∈ I`, over which the morphism to be descended is given. -/
  initial : I
  /-- The source `X₀` of the given morphism. -/
  source₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target `Y₀` of the given morphism. -/
  target₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The structure morphism `X₀ ⟶ B₀` exhibiting the source over the distinguished stage. -/
  sourceToBase : source₀ ⟶ base.obj (op initial)
  /-- The structure morphism `Y₀ ⟶ B₀` exhibiting the target over the distinguished stage. -/
  targetToBase : target₀ ⟶ base.obj (op initial)
  /-- The morphism `f₀ : X₀ ⟶ Y₀` to be descended. -/
  map₀ : source₀ ⟶ target₀
  /-- The given morphism is a morphism over the distinguished stage. -/
  map₀_over : map₀ ≫ targetToBase = sourceToBase
  /-- The source `X₀` is an algebraic space over `S`. -/
  source₀_isAlgebraicSpace : IsAlgebraicSpace B S hS source₀
  /-- The target `Y₀` is an algebraic space over `S`. -/
  target₀_isAlgebraicSpace : IsAlgebraicSpace B S hS target₀
  /-- The distinguished stage `B₀` is quasi-compact. -/
  base₀_quasiCompact : IsQuasiCompactSpace B S hS (base.obj (op initial))
  /-- The distinguished stage `B₀` is quasi-separated. -/
  base₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ (base.obj (op initial))
  /-- The source `X₀` is quasi-compact. -/
  source₀_quasiCompact : IsQuasiCompactSpace B S hS source₀
  /-- The source `X₀` is quasi-separated. -/
  source₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ source₀
  /-- The target `Y₀` is quasi-compact. -/
  target₀_quasiCompact : IsQuasiCompactSpace B S hS target₀
  /-- The target `Y₀` is quasi-separated. -/
  target₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ target₀

namespace MorphismDescentData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentData B S hS hZ I)

/-- **Stacks 07SF for Situation 084W.** Under the chapter's convention the limit `B = lim B_i`
is an algebraic space. -/
theorem isAlgebraicSpace_limit (hconv : SiteContainsBaseChangeLimits B S hS D.base) :
    IsAlgebraicSpace B S hS (limit D.base) :=
  have : Nonempty I := ⟨D.initial⟩
  isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits_of_isQuasiCompactSpace B S hS D.base
    hconv (fun i => D.base_isAlgebraicSpace i.unop) D.transition_affine (op D.initial)
    D.base₀_quasiCompact

/-- The morphism descent situation of the data of Situation 084W, the limit being an algebraic
space under the chapter's convention. -/
def toMorphismDescentSituation (hconv : SiteContainsBaseChangeLimits B S hS D.base) :
    MorphismDescentSituation B S hS hZ I where
  base := D.base
  base_isAlgebraicSpace := D.base_isAlgebraicSpace
  transition_affine := D.transition_affine
  limit_isAlgebraicSpace := D.isAlgebraicSpace_limit hconv
  initial := D.initial
  source₀ := D.source₀
  target₀ := D.target₀
  sourceToBase := D.sourceToBase
  targetToBase := D.targetToBase
  map₀ := D.map₀
  map₀_over := D.map₀_over
  source₀_isAlgebraicSpace := D.source₀_isAlgebraicSpace
  target₀_isAlgebraicSpace := D.target₀_isAlgebraicSpace
  base₀_quasiCompact := D.base₀_quasiCompact
  base₀_quasiSeparated := D.base₀_quasiSeparated
  source₀_quasiCompact := D.source₀_quasiCompact
  source₀_quasiSeparated := D.source₀_quasiSeparated
  target₀_quasiCompact := D.target₀_quasiCompact
  target₀_quasiSeparated := D.target₀_quasiSeparated

/-- The system of `AlgebraicGeometry.Space.MorphismDescentData.toMorphismDescentSituation`. -/
@[simp] theorem toMorphismDescentSituation_base
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) :
    (D.toMorphismDescentSituation hconv).base = D.base := rfl

/-- The distinguished index of
`AlgebraicGeometry.Space.MorphismDescentData.toMorphismDescentSituation`. -/
@[simp] theorem toMorphismDescentSituation_initial
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) :
    (D.toMorphismDescentSituation hconv).initial = D.initial := rfl

/-- The morphism to be descended of
`AlgebraicGeometry.Space.MorphismDescentData.toMorphismDescentSituation`. -/
@[simp] theorem toMorphismDescentSituation_map₀
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) :
    (D.toMorphismDescentSituation hconv).map₀ = D.map₀ := rfl

/-- In Situation 084W, under the chapter's convention of Section 70.2, if
`f : X ⟶ Y` is affine then `f_i : X_i ⟶ Y_i` is affine for some `i ≥ 0`. -/
@[stacks 084Y]
theorem exists_isAffineHom_mapAt (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hf : IsAffineHom B S hS (D.toMorphismDescentSituation hconv).mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsAffineHom B S hS ((D.toMorphismDescentSituation hconv).mapAt i hi) :=
  (D.toMorphismDescentSituation hconv)
    |>.exists_isAffineHom_mapAt_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits hconv hf

/-- In Situation 084W, under the chapter's convention of Section 70.2, if `f` is
finite and `f₀` is locally of finite type, then `f_i` is finite for some `i ≥ 0`. -/
@[stacks 084Z]
theorem exists_isFinite_mapAt (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hf : IsFinite B S hS (D.toMorphismDescentSituation hconv).mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsFinite B S hS ((D.toMorphismDescentSituation hconv).mapAt i hi) :=
  (D.toMorphismDescentSituation hconv).exists_isFinite_mapAt_of_siteContainsBaseChangeLimits
    hconv hf hf₀

/-- In Situation 084W, under the chapter's convention of Section 70.2, if `f` is
a closed immersion and `f₀` is locally of finite type, then `f_i` is a closed immersion for some
`i ≥ 0`. -/
@[stacks 0850]
theorem exists_isClosedImmersion_mapAt (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hf : IsClosedImmersion B S hS (D.toMorphismDescentSituation hconv).mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsClosedImmersion B S hS ((D.toMorphismDescentSituation hconv).mapAt i hi) :=
  MorphismDescentSituation.exists_isClosedImmersion_mapAt_of_siteContainsBaseChangeLimits
    (D.toMorphismDescentSituation hconv) hconv hf hf₀

/-- In Situation 084W, under the chapter's convention of Section 70.2, if `f` is
proper and `f₀` is locally of finite type, then `f_i` is proper for some `i ≥ 0`. -/
@[stacks 08K1]
theorem exists_isProper_mapAt (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hf : IsProper B S hS (D.toMorphismDescentSituation hconv).mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsProper B S hS ((D.toMorphismDescentSituation hconv).mapAt i hi) :=
  (D.toMorphismDescentSituation hconv).exists_isProper_mapAt_of_siteContainsBaseChangeLimits
    hconv hf hf₀

/-- In Situation 084W, under the chapter's convention of Section 70.2, let `F₀`
be a quasi-coherent `𝒪_{X₀}`-module of finite type and let `F` and `F_i` be its pullbacks to `X`
and `X_i`. If `f₀` is locally of finite type and the scheme-theoretic support of `F` is proper
over `Y`, then the scheme-theoretic support of `F_i` is proper over `Y_i` for some `i ≥ 0`. -/
@[stacks 08K2]
theorem exists_isProper_schemeTheoreticSupport_moduleAt
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (F₀ : Modules.{u, u} B S hS (D.toMorphismDescentSituation hconv).source₀Space.1
      (D.toMorphismDescentSituation hconv).source₀Space.2)
    (hqc : F₀.IsQuasicoherentOnSite)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (hproper : IsProper B S hS
      ((schemeTheoreticSupport B S hS (D.toMorphismDescentSituation hconv).sourceLimitSpace
        ((D.toMorphismDescentSituation hconv).moduleLimit F₀)).ι ≫
          (D.toMorphismDescentSituation hconv).mapLimit)) :
    ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS
      ((schemeTheoreticSupport B S hS ((D.toMorphismDescentSituation hconv).sourceAtSpace i hi)
        ((D.toMorphismDescentSituation hconv).moduleAt F₀ i hi)).ι ≫
          (D.toMorphismDescentSituation hconv).mapAt i hi) :=
  (D.toMorphismDescentSituation hconv)
    |>.exists_isProper_schemeTheoreticSupport_moduleAt_of_siteContainsBaseChangeLimits
      F₀ hconv hqc hf₀ hft hproper

end MorphismDescentData

end AlgebraicGeometry.Space

end
