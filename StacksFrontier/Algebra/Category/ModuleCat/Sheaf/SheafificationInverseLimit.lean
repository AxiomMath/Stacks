module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationLocality
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleInjectiveComparison

/-!
# Sheafification and inverse limits of presheaves of modules

Sheafification is a left adjoint, so it commutes with colimits and emphatically not with
limits. For a diagram `P : D ⥤ PresheafOfModules R` there is nevertheless a canonical
comparison in one direction, and only one,

`sheafificationLimitComparison P : (lim P)^# ⟶ lim (P^#)`,

the map induced on the limit by the images under sheafification of the projections of the limit
cone of `P`. It is `limit.lift` of that image cone, so it is characterised by
`sheafificationLimitComparison_π`, and it requires no hypothesis beyond the existence of the two
limits. The opposite direction is not available: there is no cone on `P` with apex
`lim (P^#)`, because the sheaves `(P j)^#` do not map to the presheaves `P j`.

## When the comparison is invertible

Not in general. `isIso_sheafificationLimitComparison_iff` says precisely when: the comparison is
invertible if and only if sheafification inverts `lim u`, the limit of the sheafification units
`u_j : P j ⟶ (P j)^#`. That is an equivalence, not a sufficient condition, so it fixes how much
any hypothesis here can be asked to do. Each `u_j` is locally bijective — that is what
sheafification means — but local bijectivity is not stable under inverse limits. Local
surjectivity is where it fails, and the failure is measured by the first derived inverse limit of
the sections: a system of locally surjective maps has a surjective limit only after an `R¹lim`
vanishes.

`isIso_sheafificationLimitComparison_of_isIso_evaluation` therefore carries a hypothesis, and
the honest one is bijectivity on the nose over a covering family rather than local
bijectivity: for some
`B : ObjectProperty C` whose objects cover every object of the site
(`GrothendieckTopology.HasEnoughObjects`, Stacks 090L (3)), the unit `u_j` is required to be
invertible on the sections over every `U` with `B U`, for every `j`. Said in words: each `P j` is
already a sheaf as far as `B` can see. That condition *is* stable under limits, because limits of
presheaves of modules are computed sectionwise, and bijectivity on the sections over each member
of `B` is what `PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation` (Stacks 0H6Y)
consumes.

Nothing here restricts the shape `D`: the statement is not about countable towers, and no
Mittag-Leffler condition appears. That is not an oversight. A tower `n ↦ H^q(-, K ⊗^𝐋 𝒪/ℐⁿ)` of
cohomology presheaves satisfies the hypothesis above because of the hypercohomology edge
isomorphism over an affine open, which is a statement about each stage separately
(`Stacks.Algebraization.homologyIso_derivedSections_of_isAffineOpen`); the `R¹lim` vanishing that
the Mittag-Leffler condition buys is needed for a *different* factor of such a comparison, the
affine-local identification of `lim_n H^q(U, K ⊗^𝐋 𝒪/ℐⁿ)` with `H^q(U, K^∧)`, and not for the
passage between `lim` and `(-)^#` recorded here.

## Relation to what the library already had

The same mathematics appears once already, welded to a cohomological situation:
`Stacks.Cohomology.DerivedLimitAcyclic.limitComparisonPresheaf` and
`Stacks.Cohomology.DerivedLimitAcyclic.isIso_sheafification_map_limitComparisonPresheaf` treat a
tower in a derived category of sheaves of modules, and their hypotheses are the Tag 0A09 package
(a Milnor triangle, invertible edge morphisms, vanishing `R¹lim`), not a condition on an
arbitrary diagram of presheaves. The comparison map itself also occurs, unnamed and not asserted
invertible, inside `Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram`. What is
new here is the statement for an arbitrary diagram of presheaves of modules, with the hypothesis
cut down to the one thing the argument uses.

## References

* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules

universe w' v u v₂ u₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w'}}
  [HasSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  {D : Type u₂} [Category.{v₂} D]

section Comparison

variable (P : D ⥤ PresheafOfModules.{w'} R.obj)
  [HasLimit P] [HasLimit (P ⋙ sheafification.{w'} (𝟙 R.obj))]

/-- **The canonical comparison from the sheafification of an inverse limit of presheaves of
modules to the inverse limit of the sheafifications.**

Sheafification of the projections of the limit cone of `P` gives a cone on `P ⋙ (-)^#` with apex
`(lim P)^#`; this is the induced map to the limit. It goes in this direction and no other, and
it is not invertible in general — see
`isIso_sheafificationLimitComparison_of_isIso_evaluation` for a condition that makes it so. -/
def sheafificationLimitComparison :
    (sheafification.{w'} (𝟙 R.obj)).obj (limit P) ⟶
      limit (P ⋙ sheafification.{w'} (𝟙 R.obj)) :=
  limit.lift _ ((sheafification.{w'} (𝟙 R.obj)).mapCone (limit.cone P))

@[reassoc (attr := simp)]
theorem sheafificationLimitComparison_π (j : D) :
    sheafificationLimitComparison P ≫ limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j =
      (sheafification.{w'} (𝟙 R.obj)).map (limit.π P j) :=
  limit.lift_π _ _

/-- The diagram of sheafification units of the stages of `P`: a map from `P` to the diagram of
underlying presheaves of the sheafifications of its stages. Its limit is the presheaf-level map
whose local bijectivity governs `sheafificationLimitComparison`. -/
@[simps]
def sheafificationUnitDiagram :
    P ⟶ (P ⋙ sheafification.{w'} (𝟙 R.obj)) ⋙
      (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj)) where
  app j := (sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.app (P.obj j)
  naturality _ _ f := (sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.naturality (P.map f)

end Comparison

section IsIso

variable (P : D ⥤ PresheafOfModules.{w'} R.obj)
  [HasLimitsOfShape D (PresheafOfModules.{w'} R.obj)]
  [HasLimitsOfShape D (SheafOfModules.{w'} R)]
  [∀ U : Cᵒᵖ, HasLimitsOfShape D (ModuleCat.{w'} (R.obj.obj U))]
  [∀ U : Cᵒᵖ, PreservesLimitsOfShape D (evaluation.{w'} R.obj U)]

omit [∀ U : Cᵒᵖ, HasLimitsOfShape D (ModuleCat.{w'} (R.obj.obj U))]
  [∀ U : Cᵒᵖ, PreservesLimitsOfShape D (evaluation.{w'} R.obj U)] in
/-- `sheafificationLimitComparison` factors as the sheafification of the limit of the
sheafification units, followed by two isomorphisms: the comparison expressing that the right
adjoint of sheafification preserves limits, and the counit of sheafification, which is
invertible. -/
theorem sheafificationLimitComparison_eq_of_preserves
    [PreservesLimitsOfShape D
      (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj))] :
    sheafificationLimitComparison P =
      (sheafification.{w'} (𝟙 R.obj)).map (limMap (sheafificationUnitDiagram P)) ≫
        (sheafification.{w'} (𝟙 R.obj)).map
          (preservesLimitIso (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj))
            (P ⋙ sheafification.{w'} (𝟙 R.obj))).inv ≫
        (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.app
          (limit (P ⋙ sheafification.{w'} (𝟙 R.obj))) := by
  refine limit.hom_ext fun j => ?_
  have hcounit : (sheafification.{w'} (𝟙 R.obj)).map
          ((SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj)).map
            (limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j)) ≫
        (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.app
          ((sheafification.{w'} (𝟙 R.obj)).obj (P.obj j)) =
      (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.app
          (limit (P ⋙ sheafification.{w'} (𝟙 R.obj))) ≫
        limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j :=
    (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.naturality
      (limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j)
  have key : limit.π P j ≫
        (sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.app (P.obj j) =
      limMap (sheafificationUnitDiagram P) ≫
        (preservesLimitIso (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj))
          (P ⋙ sheafification.{w'} (𝟙 R.obj))).inv ≫
          (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj)).map
            (limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j) := by
    rw [preservesLimitIso_inv_π, limMap_π, sheafificationUnitDiagram_app]
  rw [sheafificationLimitComparison_π]
  calc (sheafification.{w'} (𝟙 R.obj)).map (limit.π P j)
      = (sheafification.{w'} (𝟙 R.obj)).map
            (limit.π P j ≫
              (sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.app (P.obj j)) ≫
          (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.app
            ((sheafification.{w'} (𝟙 R.obj)).obj (P.obj j)) := by
        rw [Functor.map_comp, Category.assoc, Adjunction.left_triangle_components,
          Category.comp_id]
    _ = (sheafification.{w'} (𝟙 R.obj)).map
            (limMap (sheafificationUnitDiagram P) ≫
              (preservesLimitIso (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj))
                (P ⋙ sheafification.{w'} (𝟙 R.obj))).inv ≫
                (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj)).map
                  (limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j)) ≫
          (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.app
            ((sheafification.{w'} (𝟙 R.obj)).obj (P.obj j)) := by rw [key]
    _ = _ := by
        simp only [Functor.map_comp, Category.assoc, hcounit]

omit [∀ U : Cᵒᵖ, HasLimitsOfShape D (ModuleCat.{w'} (R.obj.obj U))]
  [∀ U : Cᵒᵖ, PreservesLimitsOfShape D (evaluation.{w'} R.obj U)] in
/-- **The comparison is invertible exactly when sheafification inverts the limit of the
sheafification units**, and never for any other reason: the two remaining factors of
`sheafificationLimitComparison_eq_of_preserves` are isomorphisms outright.

This is what pins down the content of
`isIso_sheafificationLimitComparison_of_isIso_evaluation` — its hypothesis is a sufficient
condition for the right-hand side here, and there is nothing else for a hypothesis to do. -/
theorem isIso_sheafificationLimitComparison_iff :
    IsIso (sheafificationLimitComparison P) ↔
      IsIso ((sheafification.{w'} (𝟙 R.obj)).map
        (limMap (sheafificationUnitDiagram P))) := by
  have : (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj)).IsRightAdjoint :=
    (sheafificationAdjunction.{w'} (𝟙 R.obj)).isRightAdjoint
  have : PreservesLimitsOfShape D
      (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj)) := inferInstance
  rw [sheafificationLimitComparison_eq_of_preserves]
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  exact IsIso.of_isIso_comp_right
    ((sheafification.{w'} (𝟙 R.obj)).map (limMap (sheafificationUnitDiagram P)))
    ((sheafification.{w'} (𝟙 R.obj)).map
          (preservesLimitIso (SheafOfModules.forget.{w'} R ⋙ restrictScalars (𝟙 R.obj))
            (P ⋙ sheafification.{w'} (𝟙 R.obj))).inv ≫
        (sheafificationAdjunction.{w'} (𝟙 R.obj)).counit.app
          (limit (P ⋙ sheafification.{w'} (𝟙 R.obj))))

/-- **The sheafification of an inverse limit of presheaves of modules is the inverse limit of
the sheafifications, as soon as every stage is already a sheaf on a covering family.**

Precisely: if the objects satisfying `B` cover every object of the site, and if for every stage
`j` of the diagram the sheafification unit `P j ⟶ (P j)^#` is invertible on the sections over
every `U` with `B U`, then `sheafificationLimitComparison P` is an isomorphism.

The hypothesis is bijectivity on the sections over the members of `B`, not local bijectivity.
Local bijectivity of the units holds automatically and does not suffice: it is not inherited by
the inverse limit, the obstruction being the first derived inverse limit of the sections. -/
theorem isIso_sheafificationLimitComparison_of_isIso_evaluation
    {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    (h : ∀ (j : D) ⦃U : C⦄, B U → IsIso ((evaluation.{w'} R.obj (op U)).map
      ((sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.app (P.obj j)))) :
    IsIso (sheafificationLimitComparison P) := by
  rw [isIso_sheafificationLimitComparison_iff]
  refine isIso_sheafification_map_of_isIso_evaluation hB _ fun U hU => ?_
  have : IsIso (Functor.whiskerRight (sheafificationUnitDiagram P)
      (evaluation.{w'} R.obj (op U))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact h j hU
  exact Stacks.HomologyComparison.isIso_map_limMap_of_isIso_whiskerRight
    (evaluation.{w'} R.obj (op U)) (sheafificationUnitDiagram P)

/-- **The sheafification of an inverse limit of presheaves of modules identified with the
inverse limit of the sheafifications**, under the hypothesis of
`isIso_sheafificationLimitComparison_of_isIso_evaluation`. -/
def sheafificationLimitIso
    {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    (h : ∀ (j : D) ⦃U : C⦄, B U → IsIso ((evaluation.{w'} R.obj (op U)).map
      ((sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.app (P.obj j)))) :
    (sheafification.{w'} (𝟙 R.obj)).obj (limit P) ≅
      limit (P ⋙ sheafification.{w'} (𝟙 R.obj)) :=
  haveI := isIso_sheafificationLimitComparison_of_isIso_evaluation P hB h
  asIso (sheafificationLimitComparison P)

@[reassoc (attr := simp)]
theorem sheafificationLimitIso_hom_π
    {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    (h : ∀ (j : D) ⦃U : C⦄, B U → IsIso ((evaluation.{w'} R.obj (op U)).map
      ((sheafificationAdjunction.{w'} (𝟙 R.obj)).unit.app (P.obj j))))
    (j : D) :
    (sheafificationLimitIso P hB h).hom ≫
        limit.π (P ⋙ sheafification.{w'} (𝟙 R.obj)) j =
      (sheafification.{w'} (𝟙 R.obj)).map (limit.π P j) :=
  sheafificationLimitComparison_π P j

end IsIso

end PresheafOfModules

end
