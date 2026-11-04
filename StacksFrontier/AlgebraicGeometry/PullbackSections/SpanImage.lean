module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily

/-!
# A generating family pulls back to a generating family

Let `f : Y ⟶ X` be a morphism of schemes, let `F` be a quasi-coherent `𝒪_X`-module and let
`U ⊆ X`, `V ⊆ Y` be affine opens with `V ≤ f⁻¹U`.
`AlgebraicGeometry.span_pullbackSection_eq_top` says that the pullbacks of *all* the sections of
`F` over `U` span `Γ(f^*F, V)` over the functions on `V`.  This file weakens the input: the
pullbacks of the members of any family that already spans `Γ(F, U)` over the functions on `U`
span `Γ(f^*F, V)` as well, and in particular a single generator pulls back to a single generator.

## Main results

* `AlgebraicGeometry.mem_span_pullbackSectionHom_image`: the pullback of any section lies in the
  span of the pullbacks of a spanning family.  This needs no affineness.
* `AlgebraicGeometry.span_pullbackSectionHom_image_eq_top`: over a compatible pair of affine
  opens, the pullbacks of a spanning family span.
* `AlgebraicGeometry.span_pullbackSectionHom_singleton_eq_top`: the case of a single generator.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) {U : X.Opens} {V : Y.Opens}

/-- **The pullback of a section lies in the span of the pullbacks of a generating family.** If a
family `s` of sections of `F` over `U` spans `Γ(F, U)` over the functions on `U`, then the
pullback of every section of `F` over `U` lies in the span, over the functions on `V`, of the
pullbacks of the members of `s`. Neither affineness nor quasi-coherence is needed. -/
public theorem mem_span_pullbackSectionHom_image (hVU : V ≤ f ⁻¹ᵁ U) (s : Set Γ(F, U))
    (hs : Submodule.span Γ(X, U) s = ⊤) (a : Γ(F, U)) :
    pullbackSectionHom f F U V hVU a ∈
      Submodule.span Γ(Y, V) (pullbackSectionHom f F U V hVU '' s) := by
  have ha : a ∈ Submodule.span Γ(X, U) s := hs ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem b hb => exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [pullbackSectionHom_smul]
    exact Submodule.smul_mem _ _ hx

/-- **The pullbacks of a generating family generate the sections of a pullback.** For a
quasi-coherent module `F` on `X`, a morphism `f : Y ⟶ X`, affine opens `U ⊆ X`, `V ⊆ Y` with
`V ≤ f⁻¹U` and a family `s` of sections of `F` over `U` spanning `Γ(F, U)` over the functions on
`U`, the sections of `f^*F` over `V` are spanned, as a module over the functions on `V`, by the
pullbacks of the members of `s`.

This weakens the hypothesis of `AlgebraicGeometry.span_pullbackSection_eq_top`, which is the
case `s = Set.univ`. -/
public theorem span_pullbackSectionHom_image_eq_top [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (s : Set Γ(F, U))
    (hs : Submodule.span Γ(X, U) s = ⊤) :
    Submodule.span Γ(Y, V) (pullbackSectionHom f F U V hVU '' s) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_pullbackSection_eq_top f F hU hV hVU]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨a, rfl⟩
  exact mem_span_pullbackSectionHom_image f F hVU s hs a

/-- **A single generator pulls back to a single generator.** If one section of `F` over the
affine open `U` spans `Γ(F, U)` over the functions on `U`, then its pullback spans the sections
of `f^*F` over the affine open `V` over the functions on `V`. -/
public theorem span_pullbackSectionHom_singleton_eq_top [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(F, U))
    (ha : Submodule.span Γ(X, U) {a} = ⊤) :
    Submodule.span Γ(Y, V) {pullbackSectionHom f F U V hVU a} = ⊤ := by
  have h := span_pullbackSectionHom_image_eq_top f F hU hV hVU {a} ha
  rwa [Set.image_singleton] at h

end AlgebraicGeometry

end
