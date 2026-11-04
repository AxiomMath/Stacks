module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionRestrictComp

/-!
# The transport along an equality of supporting closed subsets, at two nested opens

`Stacks.Gysin.supportCohomologySheaf_congr` says that `i_*ℋ ⁿ_T(ℱ)` depends on the closed subset
`T` only as a subset.  This file shows that the resulting transport along an equality `T = T'` is
natural in the coefficient module `ℱ`, composes, is carried to the transport by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and commutes with the excision
`Stacks.Gysin.supportCohomologyRestrictIso` for one open and with
`Stacks.Gysin.supportCohomologyRestrictCompIso` for two nested opens, in both directions.

## Main results

* `Stacks.Gysin.supportCohomologySheafFunctor_obj_congr`: the transport at the functor spelling of
  the cohomology sheaf, with
  `Stacks.Gysin.eqToHom_supportCohomologySheafFunctor_obj_congr` identifying it with the
  `Stacks.Gysin.supportCohomologySheaf` spelling.
* `Stacks.Gysin.supportCohomologySheaf_congr_natural`: the transport is **natural in the
  coefficient module**.
* `Stacks.Gysin.supportCohomologySheaf_congr_trans`: the transports along `T = T'` and `T' = T''`
  compose to the transport along `T = T''`.
* `Stacks.Gysin.restrictFunctor_map_supportCohomologySheaf_congr`: the restriction functor carries
  the transport to the transport.
* `Stacks.Gysin.supportCohomologySheaf_congr_supportCohomologyRestrictIso` and
  `…_supportCohomologyRestrictIso_inv`: **the transport commutes with excision**, for one open.
* `Stacks.Gysin.supportCohomologySheaf_congr_supportCohomologyRestrictCompIso` and
  `…_supportCohomologyRestrictCompIso_inv`: **the same for two nested opens** `V ⊆ W ⊆ Y`.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y : Scheme.{u}}

/-! ### The transport at the functor spelling -/

/-- **`Stacks.Gysin.supportCohomologySheaf_congr` at the functor spelling of the cohomology
sheaf.** -/
theorem supportCohomologySheafFunctor_obj_congr {T T' : Set Y} (hTT' : T = T') (hT : IsClosed T)
    (hT' : IsClosed T') (n : ℤ) (F : Y.Modules) :
    (supportCohomologySheafFunctor hT n).obj F = (supportCohomologySheafFunctor hT' n).obj F :=
  supportCohomologySheaf_congr hTT' hT hT' n F

/-- **The two spellings of the transport are the same morphism.** -/
theorem eqToHom_supportCohomologySheafFunctor_obj_congr {T T' : Set Y} (hTT' : T = T')
    (hT : IsClosed T) (hT' : IsClosed T') (n : ℤ) (F : Y.Modules) :
    eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n F) =
      eqToHom (supportCohomologySheaf_congr hTT' hT hT' n F) :=
  rfl

/-! ### Naturality and transitivity of the transport -/

/-- **The transport along an equality of supporting closed subsets is natural in the coefficient
module.** -/
theorem supportCohomologySheaf_congr_natural {T T' : Set Y} (hTT' : T = T') (hT : IsClosed T)
    (hT' : IsClosed T') (n : ℤ) {F G : Y.Modules} (φ : F ⟶ G) :
    (supportCohomologySheafFunctor hT n).map φ ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n G) =
      eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n F) ≫
        (supportCohomologySheafFunctor hT' n).map φ := by
  subst hTT'
  obtain rfl : hT' = hT := rfl
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The transports along two successive equalities of supporting closed subsets compose.** -/
theorem supportCohomologySheaf_congr_trans {T T' T'' : Set Y} (hTT' : T = T')
    (hT'T'' : T' = T'') (hT : IsClosed T) (hT' : IsClosed T') (hT'' : IsClosed T'') (n : ℤ)
    (F : Y.Modules) :
    eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n F) ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr hT'T'' hT' hT'' n F) =
      eqToHom (supportCohomologySheafFunctor_obj_congr (hTT'.trans hT'T'') hT hT'' n F) :=
  eqToHom_trans _ _

/-- **The restriction functor carries the transport to the transport.**  Restricting along an
open immersion `f` turns the transport for `T = T'` in `Y` into a morphism between the
restrictions, and that morphism is again an `eqToHom` — of the transport for the two preimages,
which are equal as subsets. -/
theorem restrictFunctor_map_supportCohomologySheaf_congr {Y' : Scheme.{u}} (f : Y' ⟶ Y)
    [IsOpenImmersion f] {T T' : Set Y} (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (n : ℤ) (F : Y.Modules) :
    (Scheme.Modules.restrictFunctor f).map
        (eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n F)) =
      eqToHom (congrArg (Scheme.Modules.restrictFunctor f).obj
        (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n F)) :=
  eqToHom_map _ _

/-! ### The transport across excision, for one open -/

/-- **The transport along an equality of supporting closed subsets commutes with excision**, for
an open subscheme `W` of `Y`: restricting the transport for `T = T'` to `W` and then excising is
excising and then transporting along the equality of the two preimages. -/
theorem supportCohomologySheaf_congr_supportCohomologyRestrictIso (W : Y.Opens) {T T' : Set Y}
    (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T') (hTW : IsClosed (W.ι ⁻¹' T))
    (hTW' : IsClosed (W.ι ⁻¹' T')) (n : ℤ) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor W.ι).map
          (eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n M)) ≫
        (supportCohomologyRestrictIso W hT' hTW' n M).hom =
      (supportCohomologyRestrictIso W hT hTW n M).hom ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr (congrArg (W.ι ⁻¹' ·) hTT') hTW hTW' n
          ((Scheme.Modules.restrictFunctor W.ι).obj M)) := by
  subst hTT'
  obtain rfl : hT' = hT := rfl
  obtain rfl : hTW' = hTW := rfl
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- `supportCohomologySheaf_congr_supportCohomologyRestrictIso` read on the inverses of the two
excisions. -/
theorem supportCohomologySheaf_congr_supportCohomologyRestrictIso_inv (W : Y.Opens)
    {T T' : Set Y} (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (hTW : IsClosed (W.ι ⁻¹' T)) (hTW' : IsClosed (W.ι ⁻¹' T')) (n : ℤ) (M : Y.Modules) :
    eqToHom (supportCohomologySheafFunctor_obj_congr (congrArg (W.ι ⁻¹' ·) hTT') hTW hTW' n
            ((Scheme.Modules.restrictFunctor W.ι).obj M)) ≫
        (supportCohomologyRestrictIso W hT' hTW' n M).inv =
      (supportCohomologyRestrictIso W hT hTW n M).inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map
          (eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n M)) :=
  (CommSq.vert_inv ⟨supportCohomologySheaf_congr_supportCohomologyRestrictIso W hTT' hT hT' hTW
    hTW' n M⟩).w

/-! ### The transport across excision, for two nested opens -/

section NestedOpens

variable (W : Y.Opens) (V : W.toScheme.Opens)

/-- **The transport along an equality of supporting closed subsets commutes with the excision for
two nested opens `V ⊆ W ⊆ Y`.**  The transport for `T = T'`, restricted along `V.ι ≫ W.ι`,
followed by the nested excision `Stacks.Gysin.supportCohomologyRestrictCompIso`, is that excision
followed by the transport along the equality of the two iterated preimages. -/
theorem supportCohomologySheaf_congr_supportCohomologyRestrictCompIso {T T' : Set Y}
    (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (hTVW' : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T')))
    (n : ℤ) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor (V.ι ≫ W.ι)).map
          (eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n M)) ≫
        (supportCohomologyRestrictCompIso W V hT' hTVW' n M).hom =
      (supportCohomologyRestrictCompIso W V hT hTVW n M).hom ≫
        eqToHom (supportCohomologySheafFunctor_obj_congr
          (congrArg (fun S ↦ V.ι ⁻¹' (W.ι ⁻¹' S)) hTT') hTVW hTVW' n
          ((Scheme.Modules.restrictFunctor (V.ι ≫ W.ι)).obj M)) := by
  subst hTT'
  obtain rfl : hT' = hT := rfl
  obtain rfl : hTVW' = hTVW := rfl
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- `supportCohomologySheaf_congr_supportCohomologyRestrictCompIso` read on the inverses. -/
theorem supportCohomologySheaf_congr_supportCohomologyRestrictCompIso_inv {T T' : Set Y}
    (hTT' : T = T') (hT : IsClosed T) (hT' : IsClosed T')
    (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (hTVW' : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T')))
    (n : ℤ) (M : Y.Modules) :
    eqToHom (supportCohomologySheafFunctor_obj_congr (congrArg (fun S ↦ V.ι ⁻¹' (W.ι ⁻¹' S)) hTT')
            hTVW hTVW' n ((Scheme.Modules.restrictFunctor (V.ι ≫ W.ι)).obj M)) ≫
        (supportCohomologyRestrictCompIso W V hT' hTVW' n M).inv =
      (supportCohomologyRestrictCompIso W V hT hTVW n M).inv ≫
        (Scheme.Modules.restrictFunctor (V.ι ≫ W.ι)).map
          (eqToHom (supportCohomologySheafFunctor_obj_congr hTT' hT hT' n M)) :=
  (CommSq.vert_inv ⟨supportCohomologySheaf_congr_supportCohomologyRestrictCompIso W V hTT' hT hT'
    hTVW hTVW' n M⟩).w

end NestedOpens

end Stacks.Gysin

end
