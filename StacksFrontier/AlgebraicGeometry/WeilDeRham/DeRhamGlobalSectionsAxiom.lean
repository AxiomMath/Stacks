module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilGlobalSections
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom

/-!
# Axiom (A8) for de Rham cohomology

Axiom (A8) of Weil cohomology theories ([Stacks, Section 0FID]) asks that for a smooth projective
`X` over `k` and `k' = Γ(X, 𝒪_X)` the map `H^0(Spec(k')) ⟶ H^0(X)` induced by `X ⟶ Spec(k')` be
an isomorphism (`Stacks.WeilCohomology.FirstChernClassData.GlobalSectionsAxiom`). For de Rham
cohomology (Section 0FWC) this is `Stacks.DeRhamWeil.bijective_pullbackPiece_zero` for the morphism
`X ⟶ Spec Γ(X, 𝒪_X)`, which is an isomorphism on global functions; this file reads it in the shape
of the base, on the degree-zero parts of `H^*_{dR}`.

## Main results

* `Stacks.WeilDeRham.deRham_globalSectionsAxiom`: **axiom (A8) for de Rham cohomology over any
  field.**

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

/-- **The degree-zero part of a pullback of de Rham cohomology is bijective as soon as the
degree-zero pullback is**: the degree-`0` part of `H^*_{dR}` is the image of `H^0_{dR}`. -/
theorem bijective_grade_zero_pullback {X T : (SmoothProjectiveScheme k).FullSubcategory}
    (g : X ⟶ T) (hg : Function.Bijective (DeRhamWeil.pullbackPiece g 0)) :
    Function.Bijective fun a : DeRhamWeil.grade T 0 =>
      (⟨DeRhamWeil.pullback g a, DeRhamWeil.pullback_mem_grade g 0 a.1 a.2⟩ :
        DeRhamWeil.grade X 0) := by
  refine ⟨?_, fun c => ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨x, rfl⟩ := (DirectSum.mem_rangeGrading k _ 0 a).1 ha
    obtain ⟨y, rfl⟩ := (DirectSum.mem_rangeGrading k _ 0 b).1 hb
    have h : DeRhamWeil.pullback g (DirectSum.of _ 0 x) =
        DeRhamWeil.pullback g (DirectSum.of _ 0 y) := congrArg Subtype.val hab
    rw [DeRhamWeil.pullback_of, DeRhamWeil.pullback_of] at h
    exact Subtype.ext (congrArg (DirectSum.of _ 0) (hg.1 (DirectSum.of_injective 0 h)))
  · obtain ⟨z, hz⟩ := (DirectSum.mem_rangeGrading k _ 0 c.1).1 c.2
    obtain ⟨x, rfl⟩ := hg.2 z
    refine ⟨⟨DirectSum.of _ 0 x, DeRhamWeil.of_mem_grade T 0 x⟩, Subtype.ext ?_⟩
    change DeRhamWeil.pullback g (DirectSum.of _ 0 x) = c.1
    rw [DeRhamWeil.pullback_of, hz]

variable (k) in
/-- **Axiom (A8) for de Rham cohomology** ([Stacks, Section 0FWC], axiom (A8) of
[Stacks, Section 0FID]): for a smooth projective `X` over a field `k` and `k' = Γ(X, 𝒪_X)`, the
map `H^0_{dR}(Spec(k')/k) ⟶ H^0_{dR}(X/k)` induced by `X ⟶ Spec(k')` is bijective. -/
theorem deRham_globalSectionsAxiom :
    (DeRhamWeil.deRhamFirstChernClassData k).GlobalSectionsAxiom := by
  intro X
  refine bijective_grade_zero_pullback (toSpecGlobalSections X)
    (DeRhamWeil.bijective_pullbackPiece_zero (toSpecGlobalSections X) ?_)
  change Function.Bijective X.obj.left.toSpecΓ.appTop.hom
  rw [Scheme.toSpecΓ_appTop]
  exact (ConcreteCategory.bijective_of_isIso _)

end Stacks.WeilDeRham

end
