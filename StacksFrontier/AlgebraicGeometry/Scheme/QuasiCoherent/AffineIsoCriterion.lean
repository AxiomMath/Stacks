module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom

/-!
# The affine criterion for invertibility at an abstract affine scheme

`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` says that on `Spec R` a
morphism of quasi-coherent modules which is invertible on global sections is invertible.  This
file removes the restriction to a literal spectrum:  the same holds on any scheme satisfying
`AlgebraicGeometry.IsAffine`, with "invertible on global sections" read as invertibility of
`AlgebraicGeometry.Scheme.Modules.Hom.app` at `⊤`, a morphism of abelian groups.

That generality is what the base-change argument needs.  The reduction of the base-change
assertion of [Stacks, Tag 02KG] to the case of two affine bases,
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_affineBases`,
hands over the *affine opens* `U` of `S` and `V` of `S'`:  `U.toScheme` satisfies `IsAffine`
but is not a literal `Spec R`, so the criterion stated for a spectrum does not apply to it.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top`:  **the criterion.**  On an
  affine scheme a morphism of quasi-coherent modules which is invertible on global sections is
  invertible.

## Implementation notes

On the quasi-coherent modules of an abstract affine scheme the global sections functor
`Γ(-, ⊤)` is faithful (`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top`) and full
(`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`);  the theorem here adds that it
reflects isomorphisms.

The proof restricts along `(isAffineOpen_top X).fromSpec : Spec Γ(X, ⊤) ⟶ X`, which is an
isomorphism by `Stacks.AlgebraicGeometry.ModuleLimits.isIso_fromSpec_top` and in particular an
open immersion, so `AlgebraicGeometry.Scheme.Modules.restrictFunctor` applies and
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor` carries quasi-coherence
across.  Restriction is used rather than pullback because its sections are *definitionally* the
sections over the image open:  `AlgebraicGeometry.Scheme.Modules.restrict_obj` is a `rfl`, and so
is `((restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U)`, which is what lets the hypothesis be
transported by a single rewrite along `Stacks.AlgebraicGeometry.ModuleLimits.image_top_fromSpec`
instead of a chain of comparison isomorphisms.  Note that the morphism itself is never rewritten:
the image notation `f ''ᵁ U` carries `IsOpenImmersion f` as an instance argument, so rewriting
`(isAffineOpen_top X).fromSpec` to the equal `X.isoSpec.inv` inside it produces a motive that
does not typecheck.

The two invertibility statements live in different concrete categories — the hypothesis in `Ab`,
and what `isIso_of_isIso_moduleSpecΓ` asks for in `ModuleCat Γ(X, ⊤)` — and the rings involved
are genuinely different, `Γ(X, ⊤)` against `Γ(Spec Γ(X, ⊤), ⊤)`.  They are crossed through
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`:  the underlying function of
`moduleSpecΓFunctor.map ψ` is the underlying function of `ψ.app ⊤`, by `rfl`, because
`AlgebraicGeometry.moduleSpecΓFunctor` only restricts the scalar action.

Reflecting invertibility back along the restriction needs nothing new either:  restriction along
an isomorphism is full and faithful by `Stacks.AlgebraicGeometry.ModuleLimits.restrictFull` and
`...restrictFaithful`, and a fully faithful functor reflects isomorphisms.  The two `IsIso`
facts are fed in positionally rather than through instance search:  the category structure on
`AlgebraicGeometry.Scheme.Modules` is a different instance from the one on `SheafOfModules`,
equal to it only after unfolding a non-reducible definition, and instance search does not see
through that.

**No `@[stacks]` attribute is placed here.**  This is one of the two sub-statements the affine
case of the base-change assertion of [Stacks, Tag 02KG] is reduced to, and not that assertion.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-- **On an affine scheme a morphism of quasi-coherent modules which is invertible on global
sections is invertible.**  This is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` with `Spec R` replaced by
an arbitrary scheme satisfying `AlgebraicGeometry.IsAffine`. -/
theorem isIso_of_isIso_app_top {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : IsIso (φ.app ⊤)) : IsIso φ := by
  have hψ : IsIso (φ.app ((isAffineOpen_top X).fromSpec ''ᵁ
      (⊤ : (Spec Γ(X, ⊤)).Opens))) := by
    rw [ModuleLimits.image_top_fromSpec]; exact h
  have hbij : Function.Bijective (ConcreteCategory.hom
      (((Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec).map φ).app ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hψ
  have hΓ : IsIso ((moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      ((Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec).map φ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hres : IsIso ((Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec).map φ) :=
    isIso_of_isIso_moduleSpecΓ _ hΓ
  exact @isIso_of_reflects_iso _ _ _ _ _ _ φ
    (Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec) hres
    (reflectsIsomorphisms_of_full_and_faithful _)

end Stacks.AlgebraicGeometry.AffineBaseChange

end
