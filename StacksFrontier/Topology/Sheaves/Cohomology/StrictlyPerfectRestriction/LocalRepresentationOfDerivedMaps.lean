module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.IteratedRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local representation of a derived morphism out of a strictly perfect complex

A morphism `α : K ⟶ L` in the derived category of modules on a ringed space whose source is a
strictly perfect complex is, locally on the space, represented by an honest morphism of
complexes: every point has a neighbourhood `U` and a morphism `β` between the restrictions of
the two complexes to `U` whose image in the derived category of `U` agrees with the restriction
of `α`, under the canonical comparison between restricting a complex and restricting its
derived image.

## Main results

* `Stacks.StrictlyPerfect.LocalRepresentation.exists_local_complex_map` is the surjectivity half of
  Tag 08C9.

## Implementation notes

The space, ring and module universes all coincide, as they already must for Tag 08C6, Tag 08C7
and Tag 08C8, on which this rests; at matching universes all sheafification instances hold
automatically and so are not hypotheses.

Writing `α` as a left fraction `Q.map γ ≫ inv (Q.map f)` makes `f` a quasi-isomorphism and so
transfers the hypotheses on cohomology to `γ`; Tag 08C8
(`Stacks.PseudoCoherence.DerivedCharacterization.exists_local_lift_homotopy`) factors `γ` through
  `f` up to homotopy over a
neighbourhood, and `AlgebraicGeometry.RingedSpace.PseudoCoherence.overFunctorIsoRestrictModules`
  carries the resulting morphism
from the slice presentation of restriction to
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`.  Homotopic maps have
equal images under `DerivedCategory.Q`, so the displayed identity follows after cancelling the
restriction of `f`, which is again a quasi-isomorphism.

## References

* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.StrictlyPerfect.LocalRepresentation

universe u d d'

variable {X : RingedSpace.{u, u}}
variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

variable {E F : CochainComplex (OXMod.{u, u} X) ℤ}

/-- **Restriction preserves finite colimits.** Restriction to an open subspace is a left
adjoint, so it preserves all colimits that exist. -/
theorem restrictModules_preservesFiniteColimits (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    PreservesFiniteColimits (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U) :=
  inferInstance

/-- **Restriction preserves finite limits.** Limits of sheaves of modules are detected by the
forgetful functor to presheaves of modules and then computed sectionwise, and a section of the
restriction over an open `V` of `U` is a section of the original module over the image of `V`. -/
theorem restrictModules_preservesFiniteLimits (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U) := by
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  exact ⟨isLimitOfReflects
    (SheafOfModules.forget (structureSheafOfRings (X.restrict U.isOpenEmbedding)))
    (PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun V =>
      isLimitOfPreserves (SheafOfModules.evaluation (structureSheafOfRings X)
        (Opposite.op (U.isOpenEmbedding.functor.obj V.unop))) hc)⟩

section Abstract

/-! ### Two general lemmas

Both steps of the argument are formal consequences of exactness, and both are stated here for
abstract abelian categories.  That is not only tidier: elaborated against
`StrictlyPerfect.OXMod` and `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` the
  same proofs cost many times the
default heartbeat budget, because every unification unfolds the ringed-space vocabulary. -/

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃]

/-- **Transporting a local homotopy lift across a factorization of the restriction functor.**
Given an isomorphism `eHC` between the complex functors of `O ⋙ T` and of `R`, and a `β` that
lifts `γ` through `f` up to homotopy after applying `O`, the conjugate of `T β` by `eHC` has
derived image composing with that of `R f` to that of `R γ`. -/
private theorem localized_comp_eq_of_homotopy
    (O : C₁ ⥤ C₂) (T : C₂ ⥤ C₃) (R : C₁ ⥤ C₃)
    [O.Additive] [T.Additive] [R.Additive] [HasDerivedCategory.{w₃} C₃]
    (eHC : O.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          T.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        R.mapHomologicalComplex (ComplexShape.up ℤ))
    {E F G : CochainComplex C₁ ℤ} (γ : E ⟶ G) (f : F ⟶ G)
    (β : (O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (O.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (hhom : Homotopy (β ≫ (O.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      ((O.mapHomologicalComplex (ComplexShape.up ℤ)).map γ)) :
    DerivedCategory.Q.map (eHC.inv.app E ≫
          (T.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫ eHC.hom.app F) ≫
        DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ) := by
  -- the naturality squares of `eHC` at `f` and at `γ`
  have hnf : (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫ eHC.hom.app G =
      eHC.hom.app F ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map f :=
    eHC.hom.naturality f
  have hnγ : (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).map γ) ≫ eHC.hom.app G =
      eHC.hom.app E ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ :=
    eHC.hom.naturality γ
  -- conjugating `T γ` by `eHC` gives `R γ` on the nose
  have hconj : eHC.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).map γ) ≫ eHC.hom.app G =
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ := by
    rw [hnγ, ← Category.assoc, eHC.inv_hom_id_app, Category.id_comp]
  -- the conjugate of `T β`, followed by `R f`, is the conjugate of `T (β ≫ O f)`
  have hcomp : (eHC.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫
        eHC.hom.app F) ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map f =
      eHC.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (β ≫ (O.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫ eHC.hom.app G := by
    rw [Functor.map_comp]
    simp only [Category.assoc, hnf]
  rw [← Functor.map_comp, hcomp, Functor.map_comp, Functor.map_comp,
    DerivedCategory.Q_map_eq_of_homotopy (C := C₃) (T.mapHomotopy hhom), ← Functor.map_comp,
    ← Functor.map_comp, hconj]

/-- **Reading off the derived identity from the localized one.** With `α` presented as the left
fraction `Q γ ≫ (Q f)⁻¹`, and `βR` a morphism of the `R`-images whose derived image satisfies
the corresponding identity, the exact functor `R` carries `α` to `βR` under the canonical
comparison `R.mapDerivedCategoryFactors`. -/
private theorem mapDerivedCategory_map_eq_of_localized
    [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂]
    (R : C₁ ⥤ C₂) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {E F G : CochainComplex C₁ ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (γ : E ⟶ G) (f : F ⟶ G) (hf : IsIso (DerivedCategory.Q.map f))
    (hα : α = DerivedCategory.Q.map γ ≫ inv (DerivedCategory.Q.map f))
    (βR : (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (hlocal : DerivedCategory.Q.map βR ≫
        DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ)) :
    R.mapDerivedCategory.map α ≫ R.mapDerivedCategoryFactors.hom.app F =
      R.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map βR := by
  have hfq : QuasiIso f :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C₁) f).mp hf
  have : R.PreservesHomology := inferInstance
  have : QuasiIso ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology f R
  have : IsIso (DerivedCategory.Q.map
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C₂) _).2 inferInstance
  have : IsIso (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) := Functor.map_isIso _ _
  -- `βR` is the left fraction built from the `R`-images
  have hβ : DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ) ≫
      inv (DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) =
      DerivedCategory.Q.map βR := by
    rw [← hlocal, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- the comparison square at `f`, with both of its isomorphism legs inverted
  have hinvnat : R.mapDerivedCategory.map (inv (DerivedCategory.Q.map f)) ≫
      R.mapDerivedCategoryFactors.hom.app F =
      R.mapDerivedCategoryFactors.hom.app G ≫
        inv (DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
    rw [Functor.map_inv, IsIso.inv_comp_eq, ← Category.assoc,
      Functor.mapDerivedCategoryFactors_hom_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [hα, Functor.map_comp, Category.assoc, hinvnat, ← Category.assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality, Category.assoc, hβ]

end Abstract

/-- The inner existential of Tag 08C9 over one open `U`, given a homotopy lift of `γ` through
`f` over `U`.  Stated separately so that `U` and the lift are chosen in
`Stacks.StrictlyPerfect.LocalRepresentation.exists_local_complex_map` by `Exists.choose`:
  destructuring them with `obtain`
against the dependent goal below would make `cases` build a motive for it, forcing its
`let`-bound instances through `whnf`. -/
private theorem local_rep_of_homotopy_lift {G : CochainComplex (OXMod.{u, u} X) ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (γ : E ⟶ G) (f : F ⟶ G) (hf : IsIso (DerivedCategory.Q.map f))
    (hα : α = DerivedCategory.Q.map γ ≫ inv (DerivedCategory.Q.map f))
    (U : Opens X.carrier)
    (β : ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ⟶
          ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F)
    (hhom : Nonempty (Homotopy
      (β ≫ ((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
      (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map γ))) :
      ∃ (hadd : (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).Additive)
        (hlim : PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules
          X U))
        (hcolim : PreservesFiniteColimits
          (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U)),
        letI := hadd
        letI := hlim
        letI := hcolim
        ∃ βR : ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
          U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E ⟶
            ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
              U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F,
          (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).mapDerivedCategory.map
            α ≫
              (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
                U).mapDerivedCategoryFactors.hom.app F =
          (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
            U).mapDerivedCategoryFactors.hom.app E ≫
              DerivedCategory.Q.map βR := by
  classical
  let hlim : PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
    U) :=
    restrictModules_preservesFiniteLimits X U
  let hcolim : PreservesFiniteColimits
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U) := inferInstance
  let hOadd : (SheafOfModules.overFunctor (structureSheafOfRings X) U).Additive :=
    ⟨by intro A B f g; ext V; rfl⟩
  let hTadd : ((AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X
    U).functor).Additive :=
    ⟨by intro A B f g; ext V; rfl⟩
  exact ⟨inferInstance, hlim, hcolim, _,
    mapDerivedCategory_map_eq_of_localized
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U) α γ f hf hα _
    (localized_comp_eq_of_homotopy (SheafOfModules.overFunctor (structureSheafOfRings X) U)
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X U).functor)
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U)
      (Functor.mapHomologicalComplexCompIso
        (AlgebraicGeometry.RingedSpace.PseudoCoherence.overFunctorIsoRestrictModules X U)
          (ComplexShape.up ℤ))
      γ f β hhom.some)⟩

/-- **The surjectivity half of Tag 08C9.** A morphism in the derived category out of a strictly
perfect complex is, over a neighbourhood of any point, represented by a morphism of complexes,
compatibly with the canonical comparison between restricting a complex and restricting its
derived image. -/
@[sga "5 IIIB 5.7" "partial"]
theorem exists_local_complex_map (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (hadd : (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).Additive)
        (hlim : PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules
          X U))
        (hcolim : PreservesFiniteColimits
          (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U)),
        letI := hadd
        letI := hlim
        letI := hcolim
        ∃ βR : ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
          U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E ⟶
            ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
              U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F,
          (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).mapDerivedCategory.map
            α ≫
              (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
                U).mapDerivedCategoryFactors.hom.app F =
          (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
            U).mapDerivedCategoryFactors.hom.app E ≫
              DerivedCategory.Q.map βR := by
  classical
  obtain ⟨G, γ, f, hf, hα⟩ := DerivedCategory.left_fac α
  have hlb := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hE
  have hfq : QuasiIso f :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := OXMod.{u, u} X) f).mp hf
  have hiso (j : ℤ) : IsIso (HomologicalComplex.homologyMap f j) :=
    (quasiIsoAt_iff_isIso_homologyMap _ j).1 (hfq.quasiIsoAt j)
  intro x
  -- `Exists.choose` rather than `obtain`: see
  -- `Stacks.StrictlyPerfect.LocalRepresentation.local_rep_of_homotopy_lift`.
  have hloc := Stacks.PseudoCoherence.DerivedCharacterization.exists_local_lift_homotopy γ f
    hlb.choose hE hlb.choose_spec (fun j _ => hiso j)
    (by have := hiso hlb.choose; infer_instance) x
  exact ⟨hloc.choose, hloc.choose_spec.1,
    local_rep_of_homotopy_lift α γ f hf hα hloc.choose
      hloc.choose_spec.2.choose hloc.choose_spec.2.choose_spec⟩

end Stacks.StrictlyPerfect.LocalRepresentation

end
