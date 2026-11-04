module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingCocycle
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexOpenCover
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingCocycleCompactifications

/-!
# Normalized dualizing complexes for the upper shriek functors of compactifications

Let `S` be Noetherian with a dualizing complex `ω_S^•`, `X` of finite type over `S`, and
`𝒰 : X = ⋃ U_i` a finite open covering by schemes separated over `S`. For the upper shriek
formalism `Stacks.Duality.UpperShriek.ofCompactifications c` attached to a compactification of
every separated finite-type morphism (Nagata's theorem [Stacks, Tag 0F41] provides one), this
file proves the statements of [Stacks, Section 0AU5] about dualizing complexes normalized
relative to `ω_S^•` and `𝒰`.

## Main results

* `Stacks.Duality.Normalized.isDualizingComplex_ofCompactifications`: a dualizing complex
  normalized relative to `ω_S^•` and `𝒰` is a dualizing complex ([Stacks, Tag 0AU5]).

## References

* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

namespace UpperShriek

/-- For an open `U ⊆ X`, the restriction `(U → X)^! K` of the formalism of compactifications is
the derived restriction of `K`, as objects of `D(𝒪_U)`. -/
def restrictToObjIso {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
    (U : X.Opens) (K : quasiCoherentDerivedCategoryPlusOfModel X) :
    ((ofCompactifications c).restrictTo hp U K).obj.obj ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K.obj.obj :=
  (ObjectProperty.ι _).mapIso ((shriekOfIsoOfIsOpenImmersion c U.ι (hp.isShriekable_ι U)).app K) ≪≫
    (OpenImmersion.restrictedDerivedRestrictCompιIso U.ι).app K.obj

end UpperShriek

/-- **Normalized complexes are dualizing ([Stacks, Tag 0AU5]).** In Situation 0AU4, for the upper
shriek functors of a choice `c` of compactifications, a dualizing complex normalized relative to
`ω_S^•` and a finite open covering `𝒰` of `X` by schemes separated over `S` is a dualizing
complex: on each `U_i` it is `(U_i → S)^! ω_S^•`, dualizing by [Stacks, Tag 0AA3], and being
dualizing is local ([Stacks, Tag 0A86]). -/
theorem Normalized.isDualizingComplex_ofCompactifications {X S : Scheme.{u}} {p : X ⟶ S}
    {hp : IsFiniteTypeOverNoetherian p} {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
    {ι : Type w} {𝒰 : SeparatedCovering p ι}
    (𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) :
    haveI := hp.source_noetherian; IsDualizingComplex 𝒩.complex.obj.obj := by
  have := hp.base_noetherian
  have := hp.source_noetherian
  refine isDualizingComplex_of_isDualizingComplex_restrict 𝒰.U 𝒰.covers fun i => ?_
  have := hp.opens_noetherian (𝒰.U i)
  have hloc : IsDualizingComplex
      ((UpperShriek.ofCompactifications c).localModel (𝒰.shriekable i) ωS).obj.obj :=
    isDualizingComplex_upperShriek_obj
      (ftsHomOf ((𝒰.U i).ι ≫ p) (𝒰.shriekable i).separatedFiniteType
        (isSeparatedFiniteType_id S) (Category.comp_id _))
      (c _ (𝒰.shriekable i)) ωS.obj hωS
  exact isDualizingComplex_of_iso
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso (𝒩.localIso i).symm ≪≫
      UpperShriek.restrictToObjIso c hp (𝒰.U i) 𝒩.complex) hloc

end Stacks.Duality

end
