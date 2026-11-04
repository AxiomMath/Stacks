module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The universe lift of sheaves of modules preserves sheafification

`ModuleCat.uliftFunctor` replaces a module by its universe lift. Mathlib records that it is fully
faithful, additive and exact, and that it preserves limits indexed by categories at the module
universe itself; nothing records how it interacts with the sheaf condition. This file supplies
that: on a site `C : Type u` with `Category.{v} C`, the universe lift of modules in a universe
`m` dominating `max u v` carries sheaves to sheaves and commutes with sheafification.

## Main results

* `ModuleCat.uliftFunctor_preservesLimitsOfSize` and
  `ModuleCat.uliftFunctor_preservesColimitsOfSize`: the universe lift of modules preserves limits
  and colimits indexed by categories whose size the module universe dominates.
* `ModuleCat.hasSheafCompose_uliftFunctor`: postcomposing a sheaf of modules with the universe
  lift gives a sheaf, so that `CategoryTheory.sheafCompose J (ModuleCat.uliftFunctor Λ)` exists.
* `ModuleCat.preservesSheafification_uliftFunctor`: the universe lift commutes with
  sheafification, which is what makes `CategoryTheory.constantCommuteCompose` available for it.

## Implementation notes

Limits and colimits of `Λ`-modules are computed on the underlying abelian groups, and
`AddCommGrpCat.uliftFunctor` preserves limits *and* colimits of arbitrary size, the latter being
the one non-formal input (Mathlib proves it from the cogenerator `ℚ/ℤ`). So both statements are
obtained from `CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves` and its dual
applied to `forget₂ (ModuleCat Λ) AddCommGrpCat`, whose reflection of limits is unconditional and
whose preservation is available once the index category is dominated by the module universe. The
natural isomorphism needed to recognize the composite is the identity: Mathlib's
`ModuleCat.uliftFunctor` and `AddCommGrpCat.uliftFunctor` are both `ULift` on the carrier, so
`ModuleCat.uliftFunctor Λ ⋙ forget₂ _ AddCommGrpCat` and
`forget₂ _ AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor` are definitionally equal.

The hypothesis is `UnivLE.{max u v, m}` rather than a module universe of the shape `max u v m'`:
the functor appearing in a goal determines `m` and the level `w` the universe is raised by, so
the instances can be matched, whereas an instance whose statement builds `m` out of the site
universes can never be — Lean has no solution for the universe constraint `max u v ?m =?= m`.
This is the same point as in
`CategoryTheory.GrothendieckTopology.hasSheafCompose_uliftFunctor`, where the lift of sheaves of
*sets* is for the same reason parametrized by the level the universe is raised by.
-/

@[expose] public section

open CategoryTheory Limits

universe w m i t v u r

namespace ModuleCat

variable (Λ : Type r) [Ring Λ]

/-- **The universe lift of modules preserves limits** indexed by a category in `Type i` whose
size the module universe dominates. Mathlib's instance is the case `i = m`. -/
theorem uliftFunctor_preservesLimitsOfSize [UnivLE.{i, m}] :
    PreservesLimitsOfSize.{t, i} (uliftFunctor.{w, m} Λ) :=
  let : PreservesLimitsOfSize.{t, i}
      (uliftFunctor.{w, m} Λ ⋙ forget₂ (ModuleCat.{max m w} Λ) AddCommGrpCat.{max m w}) := by
    show PreservesLimitsOfSize.{t, i}
      (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m} ⋙ AddCommGrpCat.uliftFunctor.{w, m})
    infer_instance
  preservesLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{max m w} Λ) AddCommGrpCat.{max m w})

/-- **The universe lift of modules preserves colimits** of a shape for which abelian groups have
them in both module universes. -/
theorem uliftFunctor_preservesColimitsOfShape (I : Type i) [Category.{t} I]
    [HasColimitsOfShape I AddCommGrpCat.{m}] [HasColimitsOfShape I AddCommGrpCat.{max m w}] :
    PreservesColimitsOfShape I (uliftFunctor.{w, m} Λ) where
  preservesColimit {K} :=
    let : PreservesColimit K
        (uliftFunctor.{w, m} Λ ⋙ forget₂ (ModuleCat.{max m w} Λ) AddCommGrpCat.{max m w}) := by
      show PreservesColimit K
        (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m} ⋙ AddCommGrpCat.uliftFunctor.{w, m})
      infer_instance
    preservesColimit_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{max m w} Λ) AddCommGrpCat.{max m w})

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The universe lift of modules carries sheaves of modules to sheaves of modules.** -/
instance hasSheafCompose_uliftFunctor [UnivLE.{max u v, m}] :
    J.HasSheafCompose (uliftFunctor.{w, m} Λ) where
  isSheaf P hP :=
    letI : PreservesLimitsOfSize.{v, max u v} (uliftFunctor.{w, m} Λ) :=
      uliftFunctor_preservesLimitsOfSize.{w, m, max u v, v, r} Λ
    Presheaf.isSheaf_comp_of_isSheaf J P _ hP

/-- **The universe lift of sheaves of modules commutes with sheafification.** -/
instance preservesSheafification_uliftFunctor [UnivLE.{max u v, m}] :
    J.PreservesSheafification (uliftFunctor.{w, m} Λ) :=
  letI : UnivLE.{max u v, max m w} := ⟨fun α ↦ small_lift.{max u v, w, m} α⟩
  letI : ∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (ModuleCat.{m} Λ)) := fun X ↦
    letI := Stacks.ConstantSheaf.preservesColimitsOfShape_forget_addCommGrp_of_univLE.{u, v, m} J X
    comp_preservesColimitsOfShape (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m})
      (forget AddCommGrpCat.{m})
  letI : ∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (ModuleCat.{max m w} Λ)) :=
    fun X ↦
      letI := Stacks.ConstantSheaf.preservesColimitsOfShape_forget_addCommGrp_of_univLE.{u, v,
        max m w} J X
      comp_preservesColimitsOfShape (forget₂ (ModuleCat.{max m w} Λ) AddCommGrpCat.{max m w})
        (forget AddCommGrpCat.{max m w})
  letI : PreservesLimitsOfSize.{max u v, max u v} (uliftFunctor.{w, m} Λ) :=
    uliftFunctor_preservesLimitsOfSize.{w, m, max u v, max u v, r} Λ
  letI : ∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (uliftFunctor.{w, m} Λ) := fun X ↦
    uliftFunctor_preservesColimitsOfShape.{w, m, max u v, max u v, r} Λ (J.Cover X)ᵒᵖ
  letI : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{m} Λ) :=
    ModuleCat.hasLimitsOfSize.{max u v, max u v, m, r}
  letI : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{max m w} Λ) :=
    ModuleCat.hasLimitsOfSize.{max u v, max u v, max m w, r}
  GrothendieckTopology.instPreservesSheafification J (uliftFunctor.{w, m} Λ)

end ModuleCat

end
