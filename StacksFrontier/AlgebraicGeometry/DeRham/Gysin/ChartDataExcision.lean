module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionCongr
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence

/-!
# Excision for `i_*ℋ ⁿ_T` along an arbitrary open immersion of schemes

`Stacks.Gysin.supportCohomologyRestrictIso` is the derived excision of [Stacks, Tag 0G78], read
on degree-`n` cohomology sheaves, for the inclusion `AlgebraicGeometry.Scheme.Opens.ι` of an open
subscheme.  This file extends it to an arbitrary open immersion of schemes, such as the leg
`AlgebraicGeometry.Scheme.homOfLE` of two nested opens `W' ≤ W`, which is not the canonical
inclusion of an open subscheme.  The extension `Stacks.Gysin.supportCohomologyOpenImmersionIso` is
in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling, and at `W.ι` it is
`supportCohomologyRestrictIso W` **by definition**.

## Main definitions

* `Stacks.Gysin.supportCohomologyOpenImmersionIso`: **excision in degree `n` along an arbitrary
  open immersion of schemes.**

## Main results

* `Stacks.Gysin.supportCohomologyRestrictIso_eq_openImmersionIso`: at the inclusion of an open
  subscheme the excision above *is* `Stacks.Gysin.supportCohomologyRestrictIso`.
* `Stacks.Gysin.modulePullbackCompConjIso_restrictFunctorIsoPullback`: the identification of the
  pullback along a composite assembled from the two factors' identifications is the identification
  of the composite.
* `Stacks.Gysin.supportCohomologyOpenImmersionIso_hom_comp`,
  `Stacks.Gysin.supportCohomologyOpenImmersionIso_eq_comp` and
  `Stacks.Gysin.supportCohomologyOpenImmersionIso_inv_comp`: **transitivity of the excision along
  a composite of two open immersions of schemes.**
* `Stacks.Gysin.supportCohomologyOpenImmersionIso_congr` and
  `Stacks.Gysin.supportCohomologyOpenImmersionIso_congr_inv`: the excision transports along an
  equality of open immersions, the reindexing being
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` on the restriction functors and
  `Stacks.Gysin.supportCohomologySheaf_congr` on the supporting closed subset.
* `Stacks.Gysin.supportCohomologyRestrictIso_hom_homOfLE` and
  `Stacks.Gysin.supportCohomologyRestrictIso_inv_homOfLE`: **the nested-chart form.**  For
  `W' ≤ W` two opens of the ambient scheme, the excision for `W'` is the excision for `W`,
  restricted along `AlgebraicGeometry.Scheme.homOfLE`, followed by the excision along that leg.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction
open Stacks.SchemeCohomology (hom)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable {X'' X' X : Scheme.{u}}

/-! ### Excision along an arbitrary open immersion of schemes -/

/-- **Excision for `i_*ℋ ⁿ_T` along an arbitrary open immersion of schemes.**  For `g : X' ⟶ X`
an open immersion of schemes, `T ⊆ X` closed and `M` a module on `X`, the restriction along `g` of
`i_*ℋ ⁿ_T(M)` is `i'_*ℋ ⁿ_{g^{-1}T}(M|_{X'})`. -/
def supportCohomologyOpenImmersionIso (g : X' ⟶ X) [IsOpenImmersion g] {T : Set X}
    (hT : IsClosed T) (hTg : IsClosed (g ⁻¹' T)) (n : ℤ) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor g).obj ((supportCohomologySheafFunctor hT n).obj M) ≅
      (supportCohomologySheafFunctor hTg n).obj ((Scheme.Modules.restrictFunctor g).obj M) :=
  supportCohomologyConjIso (hom g) (Scheme.Modules.restrictFunctorIsoPullback g).symm T hT n M

/-- **The excision along an open immersion of schemes, at the inclusion of an open subscheme, is
`Stacks.Gysin.supportCohomologyRestrictIso`.** -/
theorem supportCohomologyRestrictIso_eq_openImmersionIso {Y : Scheme.{u}} (W : Y.Opens)
    {T : Set Y} (hT : IsClosed T) (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℤ) (M : Y.Modules) :
    supportCohomologyRestrictIso W hT hTW n M =
      supportCohomologyOpenImmersionIso W.ι hT hTW n M := rfl

/-! ### The identification of the pullback along a composite -/

/-- **The identification of the pullback along a composite of open immersions of schemes with the
restriction along that composite, assembled from the two factors' identifications, is the
identification of the composite.**  Here the factors' identifications are
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, assembled by
`Stacks.Gysin.modulePullbackCompConjIso` at the factorization
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`. -/
theorem modulePullbackCompConjIso_restrictFunctorIsoPullback (f : X'' ⟶ X') (g : X' ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    modulePullbackCompConjIso (hom f) (hom g)
        (Scheme.Modules.restrictFunctorIsoPullback g).symm
        (Scheme.Modules.restrictFunctorIsoPullback f).symm
        (Scheme.Modules.restrictFunctorComp f g) =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun A => ?_))
  refine (modulePullbackCompConjIso_hom_app (hom f) (hom g)
    (Scheme.Modules.restrictFunctorIsoPullback g).symm
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
    (Scheme.Modules.restrictFunctorComp f g) A).trans ?_
  refine Eq.trans ?_ (restrictFunctorIsoPullback_inv_app_comp f g A).symm
  refine congrArg (fun ψ => (Scheme.Modules.pullbackComp f g).inv.app A ≫ ψ) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact congrArg (fun ψ => ψ ≫ (Scheme.Modules.restrictFunctorComp f g).inv.app A)
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.naturality
      ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app A))

/-! ### Transitivity along a composite of open immersions -/

section Comp

variable (f : X'' ⟶ X') (g : X' ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] {T : Set X}
  (hT : IsClosed T) (hTg : IsClosed (g ⁻¹' T)) (hTfg : IsClosed (f ⁻¹' (g ⁻¹' T))) (n : ℤ)
  (M : X.Modules)

/-- **Transitivity of the excision along a composite of two open immersions of schemes.**  The
excision for `f ≫ g` is the excision for `g`, restricted along `f`, followed by the excision for
`f` at `M|_{X'}`, with the composition isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the restriction functors mediating at
the source and at the target. -/
theorem supportCohomologyOpenImmersionIso_hom_comp :
    (supportCohomologyOpenImmersionIso (f ≫ g) hT hTfg n M).hom =
      (Scheme.Modules.restrictFunctorComp f g).hom.app
          ((supportCohomologySheafFunctor hT n).obj M) ≫
        (Scheme.Modules.restrictFunctor f).map
            (supportCohomologyOpenImmersionIso g hT hTg n M).hom ≫
          (supportCohomologyOpenImmersionIso f hTg hTfg n
              ((Scheme.Modules.restrictFunctor g).obj M)).hom ≫
            (supportCohomologySheafFunctor hTfg n).map
              ((Scheme.Modules.restrictFunctorComp f g).inv.app M) := by
  refine Eq.trans ?_ (supportCohomologyConjIso_comp (hom f) (hom g)
    (Scheme.Modules.restrictFunctorIsoPullback g).symm
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
    (Scheme.Modules.restrictFunctorComp f g) T hT n M)
  exact congrArg (fun ρ => (supportCohomologyConjIso (hom f ≫ hom g) ρ T hT n M).hom)
    (modulePullbackCompConjIso_restrictFunctorIsoPullback f g).symm

/-- `supportCohomologyOpenImmersionIso_hom_comp` as an equality of **isomorphisms**. -/
theorem supportCohomologyOpenImmersionIso_eq_comp :
    supportCohomologyOpenImmersionIso (f ≫ g) hT hTfg n M =
      (Scheme.Modules.restrictFunctorComp f g).app
          ((supportCohomologySheafFunctor hT n).obj M) ≪≫
        (Scheme.Modules.restrictFunctor f).mapIso
            (supportCohomologyOpenImmersionIso g hT hTg n M) ≪≫
          supportCohomologyOpenImmersionIso f hTg hTfg n
              ((Scheme.Modules.restrictFunctor g).obj M) ≪≫
            (supportCohomologySheafFunctor hTfg n).mapIso
              ((Scheme.Modules.restrictFunctorComp f g).app M).symm :=
  Iso.ext (supportCohomologyOpenImmersionIso_hom_comp f g hT hTg hTfg n M)

/-- **Transitivity of the excision along a composite, read on the inverses.** -/
theorem supportCohomologyOpenImmersionIso_inv_comp :
    (supportCohomologyOpenImmersionIso (f ≫ g) hT hTfg n M).inv =
      (supportCohomologySheafFunctor hTfg n).map
          ((Scheme.Modules.restrictFunctorComp f g).hom.app M) ≫
        (supportCohomologyOpenImmersionIso f hTg hTfg n
              ((Scheme.Modules.restrictFunctor g).obj M)).inv ≫
          (Scheme.Modules.restrictFunctor f).map
              (supportCohomologyOpenImmersionIso g hT hTg n M).inv ≫
            (Scheme.Modules.restrictFunctorComp f g).inv.app
              ((supportCohomologySheafFunctor hT n).obj M) := by
  rw [supportCohomologyOpenImmersionIso_eq_comp f g hT hTg hTfg n M]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  rfl

end Comp

/-! ### Transport along an equality of open immersions -/

/-- The inverse of the reindexing of the restriction functor along the trivial equality of open
immersions is the identity. -/
private theorem restrictFunctorCongr_rfl_inv (g : X' ⟶ X) [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorCongr (rfl : g = g)).inv = 𝟙 _ :=
  Iso.inv_ext (by rw [Category.comp_id, restrictFunctorCongr_rfl])

section Congr

variable {g g' : X' ⟶ X} [i : IsOpenImmersion g] [i' : IsOpenImmersion g'] (h : g = g')
  {T : Set X} (hT : IsClosed T) (hTg : IsClosed (g ⁻¹' T)) (hTg' : IsClosed (g' ⁻¹' T)) (n : ℤ)
  (M : X.Modules)

/-- **The excision transports along an equality of open immersions.**  Two equal open immersions
have equal restriction functors only up to the reindexing
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`, and equal preimages of the supporting
closed subset only up to `Stacks.Gysin.supportCohomologySheaf_congr`; this says the excision
commutes with both. -/
theorem supportCohomologyOpenImmersionIso_congr :
    (Scheme.Modules.restrictFunctorCongr h).hom.app
          ((supportCohomologySheafFunctor hT n).obj M) ≫
        (supportCohomologyOpenImmersionIso g' hT hTg' n M).hom =
      (supportCohomologyOpenImmersionIso g hT hTg n M).hom ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr (congrArg (fun u : X' ⟶ X => u ⁻¹' T) h)
            hTg hTg' n ((Scheme.Modules.restrictFunctor g).obj M)) ≫
          (supportCohomologySheafFunctor hTg' n).map
            ((Scheme.Modules.restrictFunctorCongr h).hom.app M) := by
  subst h
  obtain rfl : i = i' := rfl
  obtain rfl : hTg = hTg' := rfl
  rw [restrictFunctorCongr_rfl]
  simp only [NatTrans.id_app, Category.id_comp, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- `supportCohomologyOpenImmersionIso_congr` read on the inverses. -/
theorem supportCohomologyOpenImmersionIso_congr_inv :
    (supportCohomologySheafFunctor hTg' n).map
            ((Scheme.Modules.restrictFunctorCongr h).inv.app M) ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr
            (congrArg (fun u : X' ⟶ X => u ⁻¹' T) h).symm hTg' hTg n
            ((Scheme.Modules.restrictFunctor g).obj M)) ≫
          (supportCohomologyOpenImmersionIso g hT hTg n M).inv =
      (supportCohomologyOpenImmersionIso g' hT hTg' n M).inv ≫
        (Scheme.Modules.restrictFunctorCongr h).inv.app
          ((supportCohomologySheafFunctor hT n).obj M) := by
  subst h
  obtain rfl : i = i' := rfl
  obtain rfl : hTg = hTg' := rfl
  rw [restrictFunctorCongr_rfl_inv]
  simp only [NatTrans.id_app, Category.comp_id, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Congr

/-! ### The nested chart -/

section NestedOpens

variable {W' W : X.Opens} (e : W' ≤ W) {T : Set X} (hT : IsClosed T)
  (hTW : IsClosed (W.ι ⁻¹' T)) (hTW' : IsClosed (W'.ι ⁻¹' T))
  (hTe : IsClosed (X.homOfLE e ⁻¹' (W.ι ⁻¹' T))) (n : ℤ) (M : X.Modules)

/-- **Excision for a nested chart `W' ≤ W` of the ambient scheme.**  The excision for `W'` is the
excision for `W`, restricted along `AlgebraicGeometry.Scheme.homOfLE`, followed by the excision
along that leg, with the composition isomorphism of the restriction functors and the reindexing
along `AlgebraicGeometry.Scheme.homOfLE_ι` mediating. -/
theorem supportCohomologyRestrictIso_hom_homOfLE :
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app
          ((supportCohomologySheafFunctor hT n).obj M) ≫
        (supportCohomologyRestrictIso W' hT hTW' n M).hom =
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).hom.app
            ((supportCohomologySheafFunctor hT n).obj M) ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
              (supportCohomologyRestrictIso W hT hTW n M).hom ≫
            (supportCohomologyOpenImmersionIso (X.homOfLE e) hTW hTe n
                ((Scheme.Modules.restrictFunctor W.ι).obj M)).hom ≫
              (supportCohomologySheafFunctor hTe n).map
                ((Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).inv.app M)) ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr
            (congrArg (fun u : W'.toScheme ⟶ X => u ⁻¹' T) (X.homOfLE_ι e)) hTe hTW' n
            ((Scheme.Modules.restrictFunctor (X.homOfLE e ≫ W.ι)).obj M)) ≫
          (supportCohomologySheafFunctor hTW' n).map
            ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).hom.app M) := by
  refine (supportCohomologyOpenImmersionIso_congr (X.homOfLE_ι e) hT hTe hTW' n M).trans ?_
  rw [supportCohomologyOpenImmersionIso_hom_comp (X.homOfLE e) W.ι hT hTW hTe n M]
  rfl

/-- **Excision for a nested chart `W' ≤ W` of the ambient scheme, read on the inverses.** -/
theorem supportCohomologyRestrictIso_inv_homOfLE :
    (supportCohomologySheafFunctor hTW' n).map
            ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).inv.app M) ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr
            (congrArg (fun u : W'.toScheme ⟶ X => u ⁻¹' T) (X.homOfLE_ι e)).symm hTW' hTe n
            ((Scheme.Modules.restrictFunctor (X.homOfLE e ≫ W.ι)).obj M)) ≫
          ((supportCohomologySheafFunctor hTe n).map
              ((Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).hom.app M) ≫
            (supportCohomologyOpenImmersionIso (X.homOfLE e) hTW hTe n
                ((Scheme.Modules.restrictFunctor W.ι).obj M)).inv ≫
              (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
                  (supportCohomologyRestrictIso W hT hTW n M).inv ≫
                (Scheme.Modules.restrictFunctorComp (X.homOfLE e) W.ι).inv.app
                  ((supportCohomologySheafFunctor hT n).obj M)) =
      (supportCohomologyRestrictIso W' hT hTW' n M).inv ≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι e)).inv.app
          ((supportCohomologySheafFunctor hT n).obj M) := by
  refine Eq.trans ?_
    (supportCohomologyOpenImmersionIso_congr_inv (X.homOfLE_ι e) hT hTe hTW' n M)
  rw [supportCohomologyOpenImmersionIso_inv_comp (X.homOfLE e) W.ι hT hTW hTe n M]
  rfl

end NestedOpens

end Stacks.Gysin

end
