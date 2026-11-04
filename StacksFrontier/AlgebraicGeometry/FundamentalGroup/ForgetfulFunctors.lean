module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.FpqcCoequalizer
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.LocalCoequalizer

/-!
# Forgetful functors from finite étale covers

For a scheme `X` the two natural functors out of the category `FÉt_X` of finite étale covers of
`X` — the inclusion into `Over X` and its composite with `Over.forget X` — are exact in the
following senses. Both preserve finite colimits, the first preserves all finite limits, and the
second preserves limits of every finite connected shape.

Finite coproducts in `FÉt_X` are disjoint unions of schemes, so they are visibly preserved. For
coequalizers one uses that the underlying cofork of schemes is a coequalizer over an fpqc
covering of its target and over the pairwise overlaps, which is the descent criterion
`AlgebraicGeometry.isColimit_cofork_of_fpqc`; that local description is the content of
`Stacks.FundamentalGroup.HasFiniteColimitsWithLocalCoequalizers`, whose instance
`Stacks.FundamentalGroup.hasFiniteColimitsWithLocalCoequalizers` holds for every scheme, so all
four statements of this file are unconditional.

## Main definitions

* `AlgebraicGeometry.finiteEtaleOverForgetOver`: the forgetful functor to schemes over the base.
* `AlgebraicGeometry.finiteEtaleOverForget`: the forgetful functor to schemes.

## Main results

* `AlgebraicGeometry.isColimit_cofork_finiteEtaleOverForget`: the underlying cofork of a
  coequalizer of finite étale covers is a coequalizer of schemes.
* `AlgebraicGeometry.preservesFiniteColimits_finiteEtaleOverForgetOver` and
  `AlgebraicGeometry.preservesFiniteColimits_finiteEtaleOverForget`: preservation of finite
  colimits.
* `AlgebraicGeometry.preservesFiniteLimits_finiteEtaleOverForgetOver`: preservation of finite
  limits over the base.
* `AlgebraicGeometry.preservesFiniteConnectedLimits_finiteEtaleOverForget`: preservation of
  limits indexed by a finite connected category, in particular equalizers and fibre products.

## Implementation notes

Finite connected limits are stated one indexing category at a time, by `PreservesLimitsOfShape`
together with `FinCategory` and `IsConnected`, since there is no class for the conjunction.

The colimit statements take the fpqc-local description of the coequalizers of `FÉt_X` from the
instance of `Stacks.FundamentalGroup.HasFiniteColimitsWithLocalCoequalizers`, which is
constructed for every scheme in
`StacksFrontier/AlgebraicGeometry/FiniteEtaleColimits/LocalCoequalizer.lean`; nothing here carries a
hypothesis, and all four parts of Tag 0BNA are attached.

## References

* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BMN](https://stacks.math.columbia.edu/tag/0BMN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.FundamentalGroup (HasFiniteColimitsWithLocalCoequalizers)

universe u v

namespace AlgebraicGeometry

/-- The underlying cofork of a coequalizer of finite étale covers is a coequalizer of schemes:
it is one over an fpqc covering of its target and over the pairwise overlaps, and coequalizers
of schemes descend along fpqc coverings. -/
theorem isColimit_cofork_finiteEtaleOverForget
    {X : Scheme.{u}} {Y Z : FiniteEtaleOver X} (a b : Y ⟶ Z) (c : Cofork a b)
    (hc : IsColimit c) :
    Nonempty (IsColimit (Cofork.ofπ ((finiteEtaleOverForget X).map c.π)
      (by simpa only [← Functor.map_comp] using
        congrArg (fun k => (finiteEtaleOverForget X).map k) c.condition) :
      Cofork ((finiteEtaleOverForget X).map a) ((finiteEtaleOverForget X).map b))) := by
  obtain ⟨𝒰, hlocal, hoverlap⟩ :=
    HasFiniteColimitsWithLocalCoequalizers.exists_fpqcCover_isColimit_baseChangeCofork a b c hc
  exact isColimit_cofork_of_fpqc a.left b.left c.π.left
    (congrArg (fun k => k.left) c.condition) 𝒰.X 𝒰.f 𝒰.mem₀ hlocal hoverlap

/-- The disjoint union of a finite family of finite étale covers of `X` stays a coproduct in
`Over X`: it is already a coproduct of schemes, and `Over.forget X` reflects colimits. -/
private def forgetSigmaCoconeIsColimit {X : Scheme.{u}} {α : Type v} [Finite α]
    (D : Discrete α ⥤ FiniteEtaleOver X) :
    IsColimit ((finiteEtaleOverForgetOver X).mapCocone
      (Stacks.FundamentalGroup.sigmaCocone X D)) :=
  isColimitOfReflects (Over.forget X) (coproductIsCoproduct' _)

private instance preservesFiniteCoproductsOver {X : Scheme.{u}} :
    PreservesFiniteCoproducts (finiteEtaleOverForgetOver X) where
  preserves _ :=
    { preservesColimit := fun {D} =>
        { preserves := fun hc => ⟨IsColimit.ofIsoColimit (forgetSigmaCoconeIsColimit D)
            ((Cocone.functoriality D (finiteEtaleOverForgetOver X)).mapIso
              (hc.uniqueUpToIso (Stacks.FundamentalGroup.isColimitSigmaCocone X D))).symm⟩ } }

private instance preservesCoequalizersOver (X : Scheme.{u}) :
    PreservesColimitsOfShape WalkingParallelPair (finiteEtaleOverForgetOver X) where
  preservesColimit {K} := by
    suffices PreservesColimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) (finiteEtaleOverForgetOver X) from
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair K).symm
    refine ⟨fun {c : Cofork _ _} hc => ?_⟩
    let i : Cofork.ofπ c.π c.condition ≅ c := Cofork.ext (Iso.refl _)
    refine (isColimit_cofork_finiteEtaleOverForget _ _ _ (hc.ofIsoColimit i.symm)).map fun h =>
      isColimitOfReflects (Over.forget X)
        (((isColimitMapCoconeCoforkEquiv (finiteEtaleOverForget X) c.condition).symm h).ofIsoColimit
          ((Cocone.functoriality _ (finiteEtaleOverForget X)).mapIso i))

/-- **Stacks Project, Tag 0BNA.** The forgetful functor from finite étale covers to schemes over
the base preserves finite colimits. -/
@[stacks 0BNA "part (1), over the base"]
theorem preservesFiniteColimits_finiteEtaleOverForgetOver (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteEtaleOverForgetOver X) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    (finiteEtaleOverForgetOver X)

private instance overForgetIsLeftAdjoint (X : Scheme.{u}) : (Over.forget X).IsLeftAdjoint :=
  Adjunction.isLeftAdjoint (Over.forgetAdjStar X)

private instance overForgetPreservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (Over.forget X) where
  preservesFiniteColimits _ _ _ := inferInstance

private instance preservesFiniteColimitsOverInst (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteEtaleOverForgetOver X) :=
  preservesFiniteColimits_finiteEtaleOverForgetOver X

/-- **Stacks Project, Tag 0BNA.** The forgetful functor from finite étale covers to schemes
preserves finite colimits. -/
@[stacks 0BNA "part (1), underlying schemes"]
theorem preservesFiniteColimits_finiteEtaleOverForget (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteEtaleOverForget X) :=
  comp_preservesFiniteColimits (finiteEtaleOverForgetOver X) (Over.forget X)

/-- The forgetful functor from finite étale covers to schemes over the base preserves finite
limits. -/
@[stacks 0BNA "part (2)"]
theorem preservesFiniteLimits_finiteEtaleOverForgetOver (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteEtaleOverForgetOver X) := inferInstance

/-- The forgetful functor from finite étale covers to schemes preserves limits of every finite
connected shape, in particular equalizers and fibre products. -/
@[stacks 0BNA "part (3)"]
theorem preservesFiniteConnectedLimits_finiteEtaleOverForget
    (X : Scheme.{u}) (J : Type v) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J (finiteEtaleOverForget X) := inferInstance

end AlgebraicGeometry

end
