module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedFibreUnitAffine
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedFibreUnitLocalization

/-!
# The open-closed short exact sequence on the pro-étale site

Let `X` be a scheme, `i : Z ⟶ X` the inclusion of a closed subscheme and `j : U ⟶ X` the
inclusion of its open complement, and assume `j` quasi-compact. For every abelian sheaf `F` on
`X_proétale` the canonical sequence
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`
is short exact. This is [Stacks, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH).

The source checks exactness on the affine weakly contractible objects `V` of `X_proétale`, which
quasi-compactness of `j` splits into a part lying over `U` and a part all of whose points
specialize into the closed fibre `V ×_X Z`
(`AlgebraicGeometry.ProEtale.hasEnoughObjects_openPart_or_closedFibre`); this reduction is
`AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex_of_isIso_unit_app`. Over the second
kind of object it needs `F(V) = (i^{-1} F)(V ×_X Z)` through the unit of `i^{-1} ⊣ i_*`, which is
[Stacks, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC) together with
[Stacks, Tag 0987](https://stacks.math.columbia.edu/tag/0987). Here it is
`AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_of_specializes`: localizing at `V` reduces it
to the unit at the final object for the closed immersion `V ×_X Z ⟶ V` of affine schemes
(`AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_of_isIso_baseChange`), where it is
`AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_top`.

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_of_specializes`: the unit
  `F ⟶ i_* i^{-1} F` is invertible on sections over an affine weakly contractible object of
  `X_proétale` all of whose points specialize into its closed fibre.
* `AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`: **Stacks 09AH**.

## References

* [Stacks Project, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH)
* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
* [Stacks Project, Tag 0987](https://stacks.math.columbia.edu/tag/0987)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.ProEtale

/-- **The unit at an object specializing into its closed fibre.** Let `i : Z ⟶ X` be a closed
immersion and let `V` be an affine weakly contractible object of `X_proétale` all of whose points
specialize into `V ×_X Z`. Then for every abelian sheaf `F` on `X_proétale` the unit
`F ⟶ i_* i^{-1} F` is invertible on sections over `V`: `F(V) = (i^{-1} F)(V ×_X Z)`. -/
theorem isIso_proetaleUnit_app_of_specializes {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology X).IsWeaklyContractible V)
    (hspec : ∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
      Specializes x ((pullback.fst V.hom i).base z))
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app (op V)) := by
  have _ : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  have _ : IsClosedImmersion (pullback.fst V.hom i) := inferInstance
  have _ : IsAffine (pullback V.hom i) := isAffine_of_isAffineHom (pullback.fst V.hom i)
  refine isIso_proetaleUnit_app_of_isIso_baseChange.{u, v} i V F ?_
  exact isIso_proetaleUnit_app_top.{u, v} (pullback.fst V.hom i)
    (Scheme.ProEt.isWContractible_globalSections_of_isWeaklyContractible V hV)
    (le_ringJacobson_ker_appTop_of_specializes (pullback.fst V.hom i) hspec)
    ((Abelian.proetaleRestriction.{u, v} V.hom).obj F)

/-- **Stacks 09AH.** Let `i : Z ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open
immersion onto the complement of its image, and assume `j` quasi-compact. For every abelian sheaf
`F` on the small pro-étale site of `X` the canonical sequence
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`,
whose maps are the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*`, is short exact. -/
@[stacks 09AH]
theorem shortExact_openClosedShortComplex {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    (openClosedShortComplex.{u, v} i j hij F).ShortExact :=
  shortExact_openClosedShortComplex_of_isIso_unit_app.{u, v} i j hij
    (fun V _ hVw hspec G ↦ isIso_proetaleUnit_app_of_specializes.{u, v} i V hVw hspec G) F

end AlgebraicGeometry.ProEtale

end
