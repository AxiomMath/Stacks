module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3

/-!
# A module trivial on a closed subscheme stays trivial on its inverse image

Let `D ⊆ X` be a closed subscheme and `L` an `𝒪_X`-module whose restriction to `D` is trivial.
For a morphism `φ : X' ⟶ X` the inverse image `φ⁻¹D` is a closed subscheme of `X'`, and the
restriction of `φ^*L` to it is again trivial. In particular, if an invertible module restricts
trivially to the zero scheme of a global section, its pullback restricts trivially to the zero
scheme of the pulled-back section.

## Main results

* `Stacks.Divisors.isTrivial_pullback_subschemeι_comap` — the general statement, for a closed
  subscheme presented as an inverse image.
* `Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections` — its instance at the
  zero scheme of a pulled-back section.

## Implementation notes

The general statement takes a closed subscheme `E` of `X'` with `E = D.comap φ` rather than
`D.comap φ` itself: both `E.subscheme` and `(E.subschemeι)^*φ^*L` depend on `E`, and with `E` a
variable a different presentation of the same ideal sheaf needs no dependent rewrite.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- If `L` restricts trivially to a closed subscheme `D ⊆ X` and `E ⊆ X'` is the inverse image
of `D` along `φ : X' ⟶ X`, then `φ^*L` restricts trivially to `E`. -/
theorem isTrivial_pullback_subschemeι_comap {X X' : Scheme.{u}} (φ : X' ⟶ X)
    (D : X.IdealSheafData) (L : X.Modules) (E : X'.IdealSheafData) (hE : E = D.comap φ)
    (h : AlgebraicGeometry.SheafOfModules.IsTrivial D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback D.subschemeι).obj L)) :
    AlgebraicGeometry.SheafOfModules.IsTrivial E.subscheme.sheaf.obj
      E.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback E.subschemeι).obj ((Scheme.Modules.pullback φ).obj L)) := by
  subst hE
  have hc : ((D.comapIso φ).hom ≫ Limits.pullback.snd φ D.subschemeι) ≫ D.subschemeι =
      (D.comap φ).subschemeι ≫ φ := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  obtain ⟨ψ⟩ := AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme_of_comp
    ((D.comapIso φ).hom ≫ Limits.pullback.snd φ D.subschemeι) D.subschemeι
    ((D.comap φ).subschemeι ≫ φ) hc h
  exact ⟨(Scheme.Modules.pullbackComp (D.comap φ).subschemeι φ).app L ≪≫ ψ⟩

/-- If the invertible module `L` restricts trivially to the zero scheme of `s ∈ Γ(X, L)`, then
`φ^*L` restricts trivially to the zero scheme of `φ^*s`. -/
theorem isTrivial_pullback_zeroScheme_pullbackGlobalSections {X X' : Scheme.{u}} (φ : X' ⟶ X)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (h : AlgebraicGeometry.SheafOfModules.IsTrivial (zeroScheme X L s).subscheme.sheaf.obj
      (zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroScheme X L s).subschemeι).obj L)) :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (zeroScheme X' ((Scheme.Modules.pullback φ).obj L)
          (pullbackGlobalSections φ L s)).subscheme.sheaf.obj
      (zeroScheme X' ((Scheme.Modules.pullback φ).obj L)
          (pullbackGlobalSections φ L s)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroScheme X' ((Scheme.Modules.pullback φ).obj L)
          (pullbackGlobalSections φ L s)).subschemeι).obj
        ((Scheme.Modules.pullback φ).obj L)) :=
  isTrivial_pullback_subschemeι_comap φ (zeroScheme X L s) L _ (zeroScheme_pullback φ L s) h

end Stacks.Divisors

end
