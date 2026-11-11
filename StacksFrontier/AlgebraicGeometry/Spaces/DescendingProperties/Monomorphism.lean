module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Monomorphisms descend to a stage of a directed limit of algebraic spaces

Let `B = lim B_i` be a directed inverse limit of quasi-compact and quasi-separated algebraic
spaces over `S` with affine transition morphisms, and let `f₀ : X₀ ⟶ Y₀` be a morphism of
quasi-compact and quasi-separated algebraic spaces over one stage `B₀`. If `f₀` is locally of
finite type and its base change to `B` is a monomorphism, then its base change to some stage
`B_i` is already a monomorphism.

## Main results

* `MorphismDescentSituation.exists_mono_mapAt_of_siteContainsBaseChangeLimits`
  is Stacks 07SM, under the chapter's convention of Section 70.2 (tag 07SD), with no condition on
  the size of the index.
* `AlgebraicGeometry.Space.MorphismDescentSituation.exists_mono_mapAt`: the same for a system
  that is small for the site.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_mono_mapAt`: the same for a
  `AlgebraicGeometry.Space.MorphismDescentSystem`, whose index is bounded.

## References

* [Stacks Project, Tag 07SM](https://stacks.math.columbia.edu/tag/07SM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

end AlgebraicGeometry.Space.MorphismDescentSystem

/-! ### Descent situations with no condition on the size of the index

For `AlgebraicGeometry.Space.MorphismDescentSituation` the results take the hypothesis
`hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D.base`, and are also stated
under `hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`, which implies it. -/

namespace AlgebraicGeometry.Space.MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for presheaf pullbacks on the big fppf site needs more than the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_Monomorphism :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_Monomorphism
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 07SM.** In Situation 084W, under the chapter's convention of Section 70.2 (tag
07SD), if the base change `f` of `f₀` to the limit `B` is a monomorphism and `f₀` is locally of
finite type, then the base change `f_i` of `f₀` to some stage `B_i` is a monomorphism.

The convention of Section 70.2, that every scheme considered lies in the big fppf site, is
`hconv`: the limits of the base changes of the system to affine objects of the site lie in the
site. Nothing is asked of the size of the index. -/
@[stacks 07SM, sga "3 VIB 10.1" "partial"]
theorem exists_mono_mapAt_of_siteContainsBaseChangeLimits (hconv : SiteContainsBaseChangeLimits B S
    hS D.base) (hf : Mono D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), Mono (D.mapAt i hi) := by
  let Δ : MorphismDescentSituation B S hS hZ I :=
    { base := D.base
      base_isAlgebraicSpace := D.base_isAlgebraicSpace
      transition_affine := D.transition_affine
      limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
      initial := D.initial
      source₀ := D.source₀
      target₀ := pullback D.map₀ D.map₀
      sourceToBase := D.sourceToBase
      targetToBase := pullback.fst D.map₀ D.map₀ ≫ D.sourceToBase
      map₀ := pullback.diagonal D.map₀
      map₀_over := by simp
      source₀_isAlgebraicSpace := D.source₀_isAlgebraicSpace
      target₀_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS D.map₀ D.map₀
        D.source₀_isAlgebraicSpace D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
      base₀_quasiCompact := D.base₀_quasiCompact
      base₀_quasiSeparated := D.base₀_quasiSeparated
      source₀_quasiCompact := D.source₀_quasiCompact
      source₀_quasiSeparated := D.source₀_quasiSeparated
      target₀_quasiCompact := isQuasiCompactSpace_pullback B S hS hZ D.map₀ D.map₀
        D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace D.source₀_quasiCompact
        D.source₀_quasiCompact D.target₀_quasiSeparated
      target₀_quasiSeparated := isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ D.map₀
        D.source₀_isAlgebraicSpace D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
        D.source₀_quasiSeparated D.source₀_quasiSeparated }
  have hΔfp : IsLocallyOfFinitePresentation B S hS Δ.map₀ :=
    isLocallyOfFinitePresentation_pullbackDiagonal B S hS D.map₀
      D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace hf₀
  have hΔlim : IsIso Δ.mapLimit :=
    (isIso_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
      (limit.π D.base (op D.initial)) D.map₀ D.map₀_over D.mapLimit
      D.mapLimit_fst D.mapLimit_snd).mpr ((pullback.isIso_diagonal_iff D.mapLimit).mpr hf)
  obtain ⟨i, hi, hΔi⟩ := Δ.exists_isIso_mapAt_of_siteContainsBaseChangeLimits hconv hΔlim hΔfp
  refine ⟨i, hi, (pullback.isIso_diagonal_iff (D.mapAt i hi)).mp ?_⟩
  exact (isIso_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
    (D.baseAtToInitial i hi) D.map₀ D.map₀_over (D.mapAt i hi)
    (D.mapAt_fst i hi) (D.mapAt_snd i hi)).mp hΔi

/-- If the base change `f` of `f₀` to the limit `B` is a monomorphism and `f₀` is locally of
finite type, then the base change `f_i` of `f₀` to some stage `B_i` is a monomorphism, provided
the system is small for the site (`hb`). -/
@[sga "3 VIB 10.1" "partial"]
theorem exists_mono_mapAt (hb : IsSiteSmall B S hS D.base) (hf : Mono D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), Mono (D.mapAt i hi) :=
  have : Nonempty I := ⟨D.initial⟩
  D.exists_mono_mapAt_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) hf hf₀

end AlgebraicGeometry.Space.MorphismDescentSituation


namespace AlgebraicGeometry.Space.MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- If the base change `f` of `f₀` to the limit `B` is a monomorphism and `f₀` is locally of
finite type, then the base change `f_i` of `f₀` to some stage `B_i` is a monomorphism, for a
system whose index is bounded by the field
`AlgebraicGeometry.Space.MorphismDescentSystem.indexSize`.

Stacks 07SM itself, under the convention of Section 70.2 and with no bound on the index, is
`MorphismDescentSituation.exists_mono_mapAt_of_siteContainsBaseChangeLimits`. -/
@[sga "3 VIB 10.1" "partial"]
theorem exists_mono_mapAt (hf : Mono D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), Mono (D.mapAt i hi) :=
  D.toSituation.exists_mono_mapAt (IsSiteSmall.of_lt_cof_op D.indexSize) hf hf₀

end AlgebraicGeometry.Space.MorphismDescentSystem

end
