module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# The unit of the adjunction of a morphism restricted to a pair of opens, on sections

Let `h : X ⟶ Y` be a morphism of schemes, `U` an open of `Y`, `V` an open of `X` with
`V ≤ h⁻¹U`, and write `k := h.resLE U V e : V ⟶ U` for the induced morphism of open subschemes.
`ProjectionFormulaRestrictionSections.lean` describes the unit of `(h ∣_ U)^* ⊣ (h ∣_ U)_*` on
sections, and nothing described the unit of `k^* ⊣ k_*`.

It is not a new notion. Mathlib defines `AlgebraicGeometry.Scheme.Hom.resLE` as

> `h.resLE U V e = X.homOfLE e ≫ h ∣_ U`,

the second factor being the restriction over `U` and the first an *open immersion*, so the unit
of `k^* ⊣ k_*` is the unit of a composite, and the unit of a composite on sections is already
available for arbitrary morphisms of ringed spaces as
`Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit`. This file reads that
at the `resLE` factorisation and then removes the remaining abstract unit along `X.homOfLE e`,
which `pullbackUnit_eq` computes because that leg is an open immersion. Composing with
`pullbackRestrictIso_hom_pullbackUnit` finally expresses the unit of `k^* ⊣ k_*` through the unit
of `h^* ⊣ h_*` itself, with nothing restricted left in it except restriction maps of the module
and the two comparisons.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.RestrictionSections`.

* `resLE_toShHom`: `h.resLE U V e` is `X.homOfLE e` followed by `h ∣_ U` on the underlying
  ringed spaces, by `rfl`.
* `pullbackUnit_resLE`: **the unit of `k^* ⊣ k_*` on sections is the unit of `h ∣_ U` carried
  along the open immersion `X.homOfLE e`**, read through the composition law for pullback.
* `pullbackUnit_resLE_eq_val_map`: the same with no abstract unit left in it — the unit along
  `X.homOfLE e` is a restriction map of `(h ∣_ U)^* M` followed by the comparison of the
  concrete restriction with the abstract inverse image.
* `pullbackUnit_resLE_restrictUnit`: **the unit of `k^* ⊣ k_*` on a restricted section is the
  restriction of the unit of `h^* ⊣ h_*`.** This is the identity that relates the adjunction of
  a morphism restricted to a compatible pair of opens — the one
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomologyPullbackMap` takes `H^n` of —
  to the adjunction of the morphism itself.

## Implementation notes

*Nothing here is a fresh derivation.* The three ingredients are
`Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit` (the unit of a
composite, for arbitrary morphisms of ringed spaces and with no hypothesis), `pullbackUnit_eq`
(the unit along an open immersion, on sections) and `pullbackRestrictIso_hom_pullbackUnit` (the
restriction-inverse-image comparison on the unit). The content of this file is the observation
that `resLE` is a composite of the kind the first ingredient consumes and the composition of the
three.

*The factorisation is definitional and is recorded as such.* `resLE_toShHom` is `rfl`: `resLE` is
a composite by definition, and a composite of morphisms of schemes is the composite of the
underlying morphisms of ringed spaces on the nose. That is what lets
`modulePullbackComp_hom_app_pullbackUnit` be applied with no transport, and in particular the
open `k ⁻¹ᵁ O` is `X.homOfLE e ⁻¹ᵁ ((h ∣_ U) ⁻¹ᵁ O)` with no `eqToHom` between them.

*The morphism-level form needs no restatement, and none is given.* A consumer that has to apply a
functor — `H^n(V, -)` in
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomologyPullbackMap` — to the unit of
`k^* ⊣ k_*` wants the factorisation as an equation of *morphisms*, and that is
`Stacks.PullbackTensorComposition.modulePullbackComp_unit` applied to
`(X.homOfLE e).toLRSHom.toShHom` and `(h ∣_ U).toLRSHom.toShHom`: its `f ≫ g` is
`(h.resLE U V e).toLRSHom.toShHom` by `resLE_toShHom`, and
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction k` is
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction k.toLRSHom.toShHom`, so the
application typechecks at the `resLE` spelling with nothing in between. Restating it here would
add a declaration with no content.

*Why the statements are about sections and not about morphisms.* The inverse image
`AlgebraicGeometry.Scheme.Modules.pullback` is an abstract left adjoint, so the only handle on it
is what it does to sections through the unit; this is the discipline of
`ProjectionFormulaRestrictionSections.lean`, whose implementation notes record why `rw` is not
available on such an identity and why the proofs below are chains of `Eq.trans` and `congrArg`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction PresheafOfModules Stacks.RingedSpace
open Stacks.AlgebraicGeometry.AffinePushforward

universe u

namespace Stacks.AlgebraicGeometry.RestrictionSections

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ h ⁻¹ᵁ U)

/-- **`resLE` is an open immersion followed by the restriction over the open of the target.**
`AlgebraicGeometry.Scheme.Hom.resLE` is defined as `X.homOfLE e ≫ h ∣_ U`, and a composite of
morphisms of schemes is the composite of the underlying morphisms of ringed spaces, so this is
`rfl`. It is recorded because it is what lets the unit of a composite be read at `resLE` with no
transport between the two spellings of the open `(h.resLE U V e) ⁻¹ᵁ O`. -/
theorem resLE_toShHom :
    (h.resLE U V e).toLRSHom.toShHom =
      (X.homOfLE e).toLRSHom.toShHom ≫ (h ∣_ U).toLRSHom.toShHom :=
  rfl

/-- **The unit of `(h.resLE U V e)^* ⊣ (h.resLE U V e)_*` on sections is the unit of `h ∣_ U`
carried along the open immersion `X.homOfLE e`.** For a module `M` on the open subscheme `U` and
a section `x` of `M` over an open `O` of `U`, the composition law for pullback carries the
pullback-unit image along `X.homOfLE e` of the pullback-unit image along `h ∣_ U` of `x` to the
pullback-unit image along `h.resLE U V e` of `x`.

This is `Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit` — the unit of
a composite of morphisms of ringed spaces, on sections — read at the factorisation
`resLE_toShHom`. There is no hypothesis on `h`, on `U`, on `V` or on `M`. -/
theorem pullbackUnit_resLE (M : U.toScheme.Modules) (O : (Opens U.toScheme)ᵒᵖ)
    (x : M.val.obj O) :
    ((Stacks.DerivedPullback.Composition.modulePullbackComp
            (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom).hom.app M).val.app
        ((opensMap (X.homOfLE e).toLRSHom.toShHom).op.obj
          ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O))
        (pullbackUnit (X.homOfLE e).toLRSHom.toShHom
          ((Scheme.Modules.pullback (h ∣_ U)).obj M)
          ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O)
          (pullbackUnit (h ∣_ U).toLRSHom.toShHom M O x)) =
      pullbackUnit (h.resLE U V e).toLRSHom.toShHom M O x :=
  Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit
    (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom M O x

/-- **The unit of `(h.resLE U V e)^* ⊣ (h.resLE U V e)_*` on sections, with no abstract unit left
in it.** The leg along `X.homOfLE e` is an open immersion, so its unit is, on sections, a
restriction map of the module followed by the comparison
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` of the concrete restriction with
the abstract inverse image; that is `pullbackUnit_eq` together with `restrictUnit_eq`.

So the unit of `k^* ⊣ k_*` at a section `x` of `M` over an open `O` of `U` is: the unit of
`(h ∣_ U)^* ⊣ (h ∣_ U)_*` at `x`, restricted from `(h ∣_ U) ⁻¹ᵁ O` to the image of
`X.homOfLE e ⁻¹ᵁ ((h ∣_ U) ⁻¹ᵁ O)`, then the two comparisons. No hypothesis on anything. -/
theorem pullbackUnit_resLE_eq_val_map (M : U.toScheme.Modules) (O : (Opens U.toScheme)ᵒᵖ)
    (x : M.val.obj O) :
    pullbackUnit (h.resLE U V e).toLRSHom.toShHom M O x =
      ((Stacks.DerivedPullback.Composition.modulePullbackComp
            (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom).hom.app M).val.app
        ((opensMap (X.homOfLE e).toLRSHom.toShHom).op.obj
          ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O))
        (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE e)).hom.app
              ((Scheme.Modules.pullback (h ∣_ U)).obj M)).val
            ((opensMap (X.homOfLE e).toLRSHom.toShHom).op.obj
              ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O))
          (((Scheme.Modules.pullback (h ∣_ U)).obj M).val.map
              (homOfLE ((X.homOfLE e).image_preimage_le
                ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O).unop)).op
            (pullbackUnit (h ∣_ U).toLRSHom.toShHom M O x))) :=
  (pullbackUnit_resLE h e M O x).symm.trans
    (congrArg
      (((Stacks.DerivedPullback.Composition.modulePullbackComp
          (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom).hom.app M).val.app
        ((opensMap (X.homOfLE e).toLRSHom.toShHom).op.obj
          ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O)))
      (pullbackUnit_eq (X.homOfLE e) ((Scheme.Modules.pullback (h ∣_ U)).obj M)
        ((opensMap (h ∣_ U).toLRSHom.toShHom).op.obj O)
        (pullbackUnit (h ∣_ U).toLRSHom.toShHom M O x)))

/-- **The unit of `(h.resLE U V e)^* ⊣ (h.resLE U V e)_*` on a restricted section is the
restriction of the unit of `h^* ⊣ h_*`.** Let `H` be a module on `Y`, `W` an open of `Y` and `y`
a section of `H` over `W`. Then the unit of the twice-restricted adjunction, applied to the
restriction of `y` to `U`, is the unit of `h^* ⊣ h_*` applied to `y`, restricted twice and read
through the three comparisons: `pullbackRestrictIso` for the restriction over `U`,
`restrictFunctorIsoPullback` for the open immersion `X.homOfLE e`, and the composition law for
pullback.

This is `pullbackUnit_resLE_eq_val_map` with the one remaining unit — that of
`(h ∣_ U)^* ⊣ (h ∣_ U)_*` — replaced by `pullbackRestrictIso_hom_pullbackUnit`, and it is the
identity that relates the adjunction of a morphism restricted to a compatible pair of opens to
the adjunction of the morphism itself. There is no hypothesis on `h`, on the two opens, on `H` or
on `W`. -/
theorem pullbackUnit_resLE_restrictUnit (H : Y.Modules) (W : Y.Opens) (y : H.val.obj (op W)) :
    pullbackUnit (h.resLE U V e).toLRSHom.toShHom
        ((Scheme.Modules.restrictFunctor U.ι).obj H) (op (U.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction U.ι).unit.app H).val (op W) y) =
      ((Stacks.DerivedPullback.Composition.modulePullbackComp
              (X.homOfLE e).toLRSHom.toShHom
              (h ∣_ U).toLRSHom.toShHom).hom.app
            ((Scheme.Modules.restrictFunctor U.ι).obj H)).val.app
        ((opensMap (X.homOfLE e).toLRSHom.toShHom).op.obj
          (op ((h ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W))))
        (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE e)).hom.app
              ((Scheme.Modules.pullback (h ∣_ U)).obj
                ((Scheme.Modules.restrictFunctor U.ι).obj H))).val
            ((opensMap (X.homOfLE e).toLRSHom.toShHom).op.obj
              (op ((h ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W))))
          (((Scheme.Modules.pullback (h ∣_ U)).obj
                ((Scheme.Modules.restrictFunctor U.ι).obj H)).val.map
              (homOfLE ((X.homOfLE e).image_preimage_le
                ((h ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W)))).op
            (Hom.app ((pullbackRestrictIso h U).hom.app H).val
                (op ((h ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W)))
              (((Scheme.Modules.pullback h).obj H).val.map
                  (homOfLE (image_restrict_preimage_le h U W)).op
                (pullbackUnit h.toLRSHom.toShHom H (op W) y))))) :=
  (pullbackUnit_resLE_eq_val_map h e _ _ _).trans
    (by rw [pullbackRestrictIso_hom_pullbackUnit]; rfl)

end Stacks.AlgebraicGeometry.RestrictionSections

end
