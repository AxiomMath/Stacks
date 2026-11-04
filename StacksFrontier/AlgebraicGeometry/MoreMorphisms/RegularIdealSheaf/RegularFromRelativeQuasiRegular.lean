module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Relative
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SlicingHypotheses
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Statement 063W from its relative quasi-regular half

`Stacks.AlgebraicGeometry.Statement063W` asks, on a neighbourhood `U` of the point, both that the
closed subscheme be a relative quasi-regular immersion over the base and that it be a regular
immersion. The second is a consequence of the first: over a base to which the ambient scheme is
flat and locally of finite presentation, Stacks tag 063U turns a relative quasi-regular immersion
into a regular immersion, and the restriction `U.ι ≫ f` of the structure morphism to an open is
again flat and locally of finite presentation.

## Main results

* `Stacks.AlgebraicGeometry.statement063W_of_exists_isRelativeQuasiRegularImmersion`: a proof of
  the relative quasi-regular half of `Stacks.AlgebraicGeometry.Statement063W` yields
  `Stacks.AlgebraicGeometry.Statement063W` itself.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- **The regular half of `Stacks.AlgebraicGeometry.Statement063W` follows from its relative
quasi-regular half.** -/
theorem statement063W_of_exists_isRelativeQuasiRegularImmersion
    (h : ∀ {X S : Scheme.{u}} (f : X ⟶ S), Flat f → LocallyOfFinitePresentation f →
      ∀ (T : X.IdealSheafData), LocallyOfFinitePresentation T.subschemeι →
        ∀ (x : X) (hx : x ∈ T.support),
          (∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧ IsQuasiRegularImmersion
            (((T.comap (f.fiberι (f x))).comap V.ι).subschemeι)) →
          ((T.subschemeι ≫ f).stalkMap (⟨x, hx⟩ : T.subscheme)).hom.Flat →
          ∃ U : X.Opens, x ∈ U ∧
            IsRelativeQuasiRegularImmersion (U.ι ≫ f) (T.comap U.ι).subschemeι) :
    Statement063W.{u} := by
  intro X S f hf hfp T hT x hx hfib hflat
  obtain ⟨U, hxU, hrel⟩ := h f hf hfp T hT x hx hfib hflat
  exact ⟨U, hxU, hrel, isRegularImmersion_of_isRelativeQuasiRegularImmersion _ _ hrel⟩

end Stacks.AlgebraicGeometry

end
