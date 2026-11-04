module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RestrictedIdealTensor
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections

/-!
# The restricted multiplication of ideal sheaves on a pullback-unit section

Let `C ⊆ X` be a closed subscheme with inclusion `i`, let `I` be a closed subscheme of `X` and
let `J` be an effective Cartier divisor.  `Stacks.Divisors.restrictedIdealTensorMulIso` is the
restricted multiplication `i^*ℐ_I ⊗_{𝒪_C} i^*ℐ_J ≅ i^*ℐ_{I · J}`, and
`Stacks.Divisors.restrictedIdealMulSections` reads it on global sections.  Nothing so far said
what either of them *does* to a section.

A local section of `i^*ℐ_I` is not in general the restriction of a section of `ℐ_I`; the unit
`ℐ_I ⟶ i_*i^*ℐ_I` is only locally surjective.  On the sections that *are* in its image —
`Stacks.RingedSpace.pullbackUnit s` — the restricted multiplication is computed here: it is the
pullback-unit section of the product of the two sections inside `ℐ_{I · J}`.  Composed with
[Stacks, Tag 0C4T], whose defining factorisation
`Stacks.Divisors.unit_comp_sumKernelMap` is a statement about exactly those
sections too, this says that **the symbol of a product of pullback-unit sections is the product
of their symbols.**

## Main results

* `Stacks.Divisors.restrictedIdealTensorMulIso_hom_app_pullbackUnit` — the restricted
  multiplication carries the pure tensor of two pullback-unit sections to the pullback-unit
  section of their product; `Stacks.Divisors.restrictedIdealMulSections_pullbackUnit` is the
  same statement at the top open, where the product of global sections is named.
* `Stacks.Divisors.sumKernelMap_app_pullbackUnit` — the map of
  [Stacks, Tag 0C4T] sends a pullback-unit section to the class of the section it comes from.
* `Stacks.Divisors.sumKernelMap_app_restrictedIdealMulSections` — **the two
  together**: the [Stacks, Tag 0C4T] symbol of `restrictedIdealMulSections` applied to two
  pullback-unit sections is the class of the product of the two sections of the ideal sheaves.

## What this does not give

The three results above are about the sections of `i^*ℐ_I` that come from `Γ(X, ℐ_I)`.  That
for *every* pair of symbols the symbol of the product of two lifts is
`Stacks.Divisors.restrictedIdealMulSections` of the two is not proved here: passing from these
sections to all of them needs a form of the statement over an arbitrary open and a gluing
argument, and neither is here.  It is
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`, in
`StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`, which glues over the affine
opens of the ambient scheme rather than over the opens of `C` — so the local generation of
`Stacks.PullbackUnitGenerators.exists_mem_span` is not what it uses.  Nothing here carries a
`@[stacks]` attribute.

## Implementation notes

**Where the two spellings of the tensor product are crossed.** The source of
`Stacks.RingedSpace.comparison` is the bifunctor spelling
`(tensorSheaf X).obj (A, B)`, while `Stacks.Divisors.restrictedIdealTensorMulIso` is typed at
the monoidal product `⊗` of the re-seated structure, as prescribed in the module docstring of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal`.  No `rw` below
crosses between them: the single crossing is the statement of
`restrictedIdealTensorMulIso_hom_comparison`, whose proof is `Iso.hom_inv_id_assoc` and whose
`:=` tolerates the definitional equality, and every later step is a term built from it by
`PresheafOfModules.comp_app_apply` and `PresheafOfModules.hom_congr_apply'`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

universe u

namespace Stacks.Divisors

-- The monoidal structure of [Stacks, Tag 01CA] on `Mod(𝒪_Z)`, named in
-- `StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RestrictedIdealTensor`, put back
-- where instance search can see it: it is the one the type of
-- `Stacks.Divisors.restrictedIdealTensorMulIso` is spelled at.
attribute [local instance] Stacks.PullbackSheafTensor.monoidalSheafTensor

variable {X : Scheme.{u}}

/-- **The comparison of [Stacks, Tag 01CD] followed by the restricted multiplication is the
pullback of the multiplication.** This is the one place where the two spellings of the tensor
product meet: the left-hand side is typed at the monoidal product `⊗`, the identity itself is
`Iso.hom_inv_id_assoc`, and every statement below is a term built from this one. -/
theorem restrictedIdealTensorMulIso_hom_comparison (C I J : X.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J) :
    Stacks.PullbackSheafTensor.sheafTensorComparison C.subschemeι.toLRSHom.toShHom
          (idealSheafOfModules I) (idealSheafOfModules J) ≫
        (restrictedIdealTensorMulIso C I J hJ).hom =
      (pullbackFunctor C.subschemeι.toLRSHom.toShHom).map (idealTensorMul I J) :=
  Iso.hom_inv_id_assoc (Stacks.PullbackSheafTensor.sheafTensorComparisonIso
    C.subschemeι.toLRSHom.toShHom (idealSheafOfModules I) (idealSheafOfModules J)) _

/-- **The restricted multiplication on a pure tensor of pullback-unit sections.** The product of
the restriction of a section `s` of `ℐ_I` with the restriction of a section `t` of `ℐ_J` is the
restriction of their product inside `ℐ_{I · J}`. -/
theorem restrictedIdealTensorMulIso_hom_app_pullbackUnit (C I J : X.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J) (U : (Opens X.carrier)ᵒᵖ)
    (s : (idealSheafOfModules I).val.obj U) (t : (idealSheafOfModules J).val.obj U) :
    ((restrictedIdealTensorMulIso C I J hJ).hom.val.app _).hom
        (toTensorSheafSection C.subscheme.toRingedSpace
          ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
          ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J)) _
          (pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist I) U s ⊗ₜ
            pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist J) U t)) =
      pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist (I * J)) U
        (((idealTensorMul I J).val.app U).hom
          (toTensorSheafSection X.toRingedSpace (idealSheafOfModules I)
            (idealSheafOfModules J) U (s ⊗ₜ t))) := by
  refine Eq.trans (congrArg
    (fun w => ((restrictedIdealTensorMulIso C I J hJ).hom.val.app _).hom w)
    (Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul C.subschemeι.toLRSHom.toShHom
      (idealSheafOfModules I) (idealSheafOfModules J) U s t)).symm ?_
  refine Eq.trans (Eq.trans (PresheafOfModules.comp_app_apply _ _ _ _).symm
    (PresheafOfModules.hom_congr_apply'
      (congrArg SheafOfModules.Hom.val (restrictedIdealTensorMulIso_hom_comparison C I J hJ))
      _ _)) ?_
  exact Stacks.RingedSpace.pullbackUnit_naturality C.subschemeι.toLRSHom.toShHom
    (idealTensorMul I J) U _

/-- **The restricted multiplication of two global pullback-unit sections**, in the form in
which `Stacks.Divisors.restrictedIdealMulSections` names it. -/
theorem restrictedIdealMulSections_pullbackUnit (C I J : X.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J)
    (s : (idealSheafOfModules I).val.obj (op (⊤ : X.Opens)))
    (t : (idealSheafOfModules J).val.obj (op (⊤ : X.Opens))) :
    restrictedIdealMulSections C I J hJ
        (pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist I) (op (⊤ : X.Opens)) s)
        (pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist J) (op (⊤ : X.Opens)) t) =
      pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist (I * J)) (op (⊤ : X.Opens))
        (((idealTensorMul I J).val.app (op (⊤ : X.Opens))).hom
          (toTensorSheafSection X.toRingedSpace (idealSheafOfModules I)
            (idealSheafOfModules J) (op (⊤ : X.Opens)) (s ⊗ₜ t))) :=
  restrictedIdealTensorMulIso_hom_app_pullbackUnit C I J hJ (op (⊤ : X.Opens)) s t

/-- **The map of [Stacks, Tag 0C4T] on a pullback-unit section.** It sends the restriction to
`C` of a section `s` of `ℐ_D` to the class of `s` modulo `ℐ_{C + D}`. This is the defining
factorisation `Stacks.Divisors.unit_comp_sumKernelMap`, read on sections. -/
theorem sumKernelMap_app_pullbackUnit (C D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (U : X.Opens)
    (s : (idealSheafOfModules D).val.obj (op U)) :
    ((sumKernelMap D C hD).val.app (op U)).hom
        (pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist D) (op U) s) =
      (C * D).subschemeι.app U (idealSheafSection D s) :=
  Eq.trans (PresheafOfModules.comp_app_apply _ _ _ _).symm
    (PresheafOfModules.hom_congr_apply' (congrArg SheafOfModules.Hom.val
      (unit_comp_sumKernelMap D C hD)) (op U) s)

/-- **The symbol of a product of pullback-unit sections is the product of their symbols.** For
`s` a global section of `ℐ_I` and `t` one of `ℐ_J`, the [Stacks, Tag 0C4T] symbol in
`Γ(𝒪_{C + I + J})` of the restricted product of their restrictions to `C` is the class of the
product `s t`.

This is the content of the identification of the pairing on the graded pieces with
`Stacks.Divisors.restrictedIdealMulSections`, for the sections that come from `X`.  The map on
global sections `Stacks.Divisors.addEffectiveCartierDivisorSections` is this morphism's value
at `⊤`, so a consumer stated with it uses this with no transport. -/
theorem sumKernelMap_app_restrictedIdealMulSections (C I J : X.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J) (hIJ : IsEffectiveCartierDivisor (I * J))
    (s : (idealSheafOfModules I).val.obj (op (⊤ : X.Opens)))
    (t : (idealSheafOfModules J).val.obj (op (⊤ : X.Opens))) :
    ((sumKernelMap (I * J) C hIJ).val.app (op (⊤ : X.Opens))).hom
        (restrictedIdealMulSections C I J hJ
          (pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist I) (op (⊤ : X.Opens)) s)
          (pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist J) (op (⊤ : X.Opens)) t)) =
      (C * (I * J)).subschemeι.app ⊤ (idealSheafSection I s * idealSheafSection J t) := by
  refine Eq.trans (congrArg
    (((sumKernelMap (I * J) C hIJ).val.app (op (⊤ : X.Opens))).hom)
    (restrictedIdealMulSections_pullbackUnit C I J hJ s t)) ?_
  refine Eq.trans (sumKernelMap_app_pullbackUnit C (I * J) hIJ ⊤ _) ?_
  refine congrArg ((C * (I * J)).subschemeι.app ⊤) ?_
  exact Eq.trans (idealSheafSection_idealTensorMul I J ⊤ _)
    (idealTensorToUnit_app_tmul I J ⊤ s t)

end Stacks.Divisors

end
