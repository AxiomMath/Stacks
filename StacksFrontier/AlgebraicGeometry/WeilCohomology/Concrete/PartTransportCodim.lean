module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionClassCodimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityUnitName
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Gysin pullback to the parts of a product of equidimensional schemes

Let `X` and `Y` be smooth projective over a field `k`, equidimensional of dimensions `d` and `e`,
so that the inclusion `ι = partι X d ⊗ partι Y e : X_d × Y_e ⟶ X × Y` of the product of their
parts of dimensions `d` and `e` is an isomorphism. A correspondence on the block `(d, e)` of
`Corrʳ(X, Y) = ⊕_{d', e'} CH_{e'-r}(X_{d'} × Y_{e'}) ⊗ ℚ` is a class `α` on `X_d × Y_e`; the
identification `corrEquivCorrespondence` transports it to `X × Y` along `ι`. The Gysin map `ι^!`
of Stacks 0FF3 undoes that transport on classes read in codimension.

## Main results

* `Stacks.WeilCohomology.codimensionGysin_chowGroupToCodimension_chowPushforwardOfIso`: for an
  isomorphism `j : U ⟶ X` of smooth schemes, `j^!` of the codimension reading of `j_*α` is the
  codimension reading of `α`.
* `Stacks.WeilCohomology.codimensionGysin_chowGroupToCodimension_partTransport`: the same for
  `ι : X_d × Y_e ⟶ X × Y` and the transport used by `corrEquivCorrespondence`.
* `Stacks.WeilCohomology.corrToCodimChow_lof_lof_tmul`: `corrToCodimChow` on the block `(d, e)`.

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Iso

variable {k : Type u} [Field k] {X U : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sU : U ⟶ (fieldChowSituation k).S) [Smooth sU] (j : U ⟶ X) [IsIso j]
  (hj : j ≫ sX = sU)

/-- **The Gysin map of an isomorphism undoes the pushforward along it, on classes read in
codimension.** For an isomorphism `j : U ⟶ X` of schemes smooth over `k` and `α ∈ CH_l(U)`, the
Gysin map `j^!` carries the class of `j_*α`, read in codimension `i`, to the class of `α` read in
codimension `i`. -/
theorem codimensionGysin_chowGroupToCodimension_chowPushforwardOfIso (l i : ℤ)
    (α : chowGroup (fieldChowSituation k) sU l) :
    codimensionGysin sU sX hj i
        (chowGroupToCodimension sX l i
          (chowPushforwardOfIso (fieldChowSituation k) sU sX j hj l α)) =
      chowGroupToCodimension sU l i α := by
  funext p
  rw [codimensionGysin_of_isOpenImmersion]
  by_cases h : l = p - i
  · rw [chowGroupToCodimension_apply_of_eq sX l i _ p h,
      chowGroupToCodimension_apply_of_eq sU l i α p h,
      chowGroupRestrict_chowGroupDegreeEquiv, chowGroupRestrict_comp,
      chowGroupRestrict_congr (fieldChowSituation k) sX (partBase sU p)
        (dimPartMap sX sU hj p ≫ (dimPart sX p).ι) _ l ((dimPart sU p).ι ≫ j)
        (dimPartMap_ι sX sU hj p) (by rw [Category.assoc, hj]),
      ← chowGroupRestrict_comp (fieldChowSituation k) sX sU j hj,
      chowGroupRestrict_chowPushforwardOfIso]
  · rw [chowGroupToCodimension_apply_of_ne sX l i _ p h,
      chowGroupToCodimension_apply_of_ne sU l i α p h,
      map_zero]

end Iso

section Parts

open MonoidalCategory SmoothProjectiveScheme

variable {k : Type u} [Field k] {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
  (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)

/-- **The Gysin map along `X_d × Y_e ⟶ X × Y` undoes the transport of a class to `X × Y`.**
For `X` and `Y` equidimensional of dimensions `d` and `e`, the inclusion
`ι = partι X d ⊗ partι Y e : X_d × Y_e ⟶ X × Y` is an isomorphism. For `α ∈ CH_l(X_d × Y_e)`, the
transport of `α` to `X × Y` along `ι` (the one used by `corrEquivCorrespondence` on the block
`(d, e)`), read in codimension `i`, has Gysin pullback along `ι` the class of `α` read in
codimension `i`. -/
theorem codimensionGysin_chowGroupToCodimension_partTransport (l i : ℤ)
    (α : chowGroup (fieldChowSituation k)
      (pullback.fst (part X d).obj.hom (part Y e).obj.hom ≫ (part X d).obj.hom) l) :
    haveI := isIso_dimPart_self_ι X.obj.hom hX
    haveI := isIso_dimPart_self_ι Y.obj.hom hY
    codimensionGysin (part X d ⊗ part Y e).obj.hom (X ⊗ Y).obj.hom
        (Over.w (partι X d ⊗ₘ partι Y e).hom) i
        (chowGroupToCodimension (X ⊗ Y).obj.hom l i
          (chowPushforwardOfIso (fieldChowSituation k)
            (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e))
            (prodBase X.obj.hom Y.obj.hom)
            (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d) (partBase Y.obj.hom e)
              (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl)
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) l α)) =
      chowGroupToCodimension (part X d ⊗ part Y e).obj.hom l i α := by
  have := isIso_dimPart_self_ι X.obj.hom hX
  have := isIso_dimPart_self_ι Y.obj.hom hY
  have : IsIso (partι X d ⊗ₘ partι Y e).hom.left :=
    inferInstanceAs (IsIso (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d)
      (partBase Y.obj.hom e) (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl))
  exact codimensionGysin_chowGroupToCodimension_chowPushforwardOfIso _ _ _ _ l i α

/-- **`corrToCodimChow` on the block `(d, e)`.** For `X` and `Y` equidimensional of dimensions `d`
and `e`, the correspondence `q ⊗ α` on the block `(d, e)` of `Corrʳ(X, Y)`, for an integral class
`α ∈ CH_{e-r}(X_d × Y_e)`, goes to `q` times the class in `CH^{d+r}(X × Y) ⊗ ℚ` of the transport
of `α` to `X × Y`, read in codimension `d + r`. -/
theorem corrToCodimChow_lof_lof_tmul (r : ℤ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k)
      (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e)) ((e : ℤ) - r)) :
    haveI := isIso_dimPart_self_ι X.obj.hom hX
    haveI := isIso_dimPart_self_ι Y.obj.hom hY
    corrToCodimChow hX hY r ((SmoothProjectiveCorr.toCorr X Y r).symm
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))) =
      q • codimensionToCodimChow k (X ⊗ Y).obj.hom ((d : ℤ) + r)
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - r) ((d : ℤ) + r)
          (chowPushforwardOfIso (fieldChowSituation k)
            (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e))
            (prodBase X.obj.hom Y.obj.hom)
            (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d) (partBase Y.obj.hom e)
              (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl)
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) ((e : ℤ) - r) α)) := by
  have := isIso_dimPart_self_ι X.obj.hom hX
  have := isIso_dimPart_self_ι Y.obj.hom hY
  rw [corrToCodimChow_apply, LinearEquiv.apply_symm_apply, corrEquivCorrespondence_lof_lof,
    correspondenceEquivOfIso_tmul, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    rationalCodimensionToCodimChow_tmul]

end Parts

end Stacks.WeilCohomology

end
