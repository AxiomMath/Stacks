module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties

/-!
# Trivializing a pulled-back invertible module

A trivialization `M ≅ 𝒪_Y` of a module on `Y` pulls back to a trivialization of `f^* M` on `X`,
and under it the pullback `f^* s` of a section is represented by the pullback `f^# a` of the
function representing `s`. This is the step that turns the universal section of the Bertini
situation ([Stacks, Tag 0G47]) into the universal linear form on a chart.

## Main definitions

* `Stacks.Divisors.pullbackFrameSections` is the resulting `Γ(X, ⊤)`-linear equivalence
  `Γ(f^* M, ⊤) ≃ₗ Γ(X, ⊤)`.

## Main results

* `Stacks.Divisors.pullbackFrameSections_pullbackGlobalSections`: the equivalence carries
  `f^* s` to `f^# (e s)`.
* `Stacks.Divisors.pullbackFrameSections_sum_smul` and
  `Stacks.Divisors.zeroScheme_ideal_top_sum_smul`: on an affine `X` the zero scheme of a linear
  combination `∑ᵢ cᵢ · f^* sᵢ` is cut out by `∑ᵢ cᵢ · f^# aᵢ`.

## Implementation notes

The equivalence is the composite of `(f^* e)` with the comparison `f^* 𝒪_Y ⟶ 𝒪_X`, both of
which are isomorphisms — the second because the preimage functor on opens is final. Its value
on a pulled-back section is `Stacks.Divisors.pullbackGlobalSections_frame_appTop`.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
  (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)

section Frame

/-- The pushforward of sheaves of modules along a morphism of schemes is a right adjoint. -/
instance isRightAdjoint_pushforward :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

/-- The preimage functor on opens along `f` is final. -/
instance final_opensMap_base : (TopologicalSpace.Opens.map f.base).Final :=
  Stacks.Topology.final_opensMap f.base

/-- The comparison `f^* 𝒪_Y ⟶ 𝒪_X`, which is an isomorphism. -/
def unitComparison : (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
    SheafOfModules.unit X.ringCatSheaf :=
  SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingCatSheafHom

/-- The comparison `f^* 𝒪_Y ⟶ 𝒪_X` is an isomorphism. -/
instance isIso_unitComparison : IsIso (unitComparison f) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom

/-- **The pullback of a trivialization.** The isomorphism `f^* M ≅ 𝒪_X` obtained by pulling
back a trivialization `M ≅ 𝒪_Y`. -/
def pullbackFrameIso :
    (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ asIso (unitComparison f)

/-- The isomorphism `f^* M ≅ 𝒪_X` of `Stacks.Divisors.pullbackFrameIso`, as a morphism. -/
def pullbackFrame : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (pullbackFrameIso f M e).hom

/-- The morphism `f^* M ⟶ 𝒪_X` pulled back from a trivialization of `M` is an isomorphism. -/
instance isIso_pullbackFrame : IsIso (pullbackFrame f M e) :=
  (pullbackFrameIso f M e).isIso_hom

/-- **The pullback of a trivialization trivializes the pullback**, read on global sections. -/
def pullbackFrameSections :
    Γ((Scheme.Modules.pullback f).obj M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  haveI : IsIso ((pullbackFrame f M e).app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp (isIso_pullbackFrame f M e) ⊤
  LinearEquiv.ofBijective
    ({ toFun := fun t => (pullbackFrame f M e).app ⊤ t
       map_add' := fun a b => map_add _ a b
       map_smul' := fun r t => Scheme.Modules.Hom.app_smul (pullbackFrame f M e) r t } :
      Γ((Scheme.Modules.pullback f).obj M, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤))
    (ConcreteCategory.bijective_of_isIso ((pullbackFrame f M e).app ⊤))

/-- The equivalence `Stacks.Divisors.pullbackFrameSections` is the action of
`Stacks.Divisors.pullbackFrame` on global sections. -/
@[simp]
theorem pullbackFrameSections_apply (t : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    pullbackFrameSections f M e t = (pullbackFrame f M e).app ⊤ t := rfl

/-- **The pullback of a section is represented by the pullback of its function.** Under
`Stacks.Divisors.pullbackFrameSections`, the pullback `f^* s` corresponds to `f^# (e s)`. -/
theorem pullbackFrameSections_pullbackGlobalSections (s : Γ(M, ⊤)) :
    pullbackFrameSections f M e (pullbackGlobalSections f M s) =
      f.appTop (e.hom.app ⊤ s) :=
  pullbackGlobalSections_frame_appTop f M e s

end Frame

section LinearCombination

variable {ι : Type*} [Fintype ι]

/-- **The function representing a linear combination of pulled-back sections.** -/
theorem pullbackFrameSections_sum_smul (c : ι → Γ(X, ⊤)) (s : ι → Γ(M, ⊤)) :
    pullbackFrameSections f M e (∑ i, c i • pullbackGlobalSections f M (s i)) =
      ∑ i, c i * f.appTop (e.hom.app ⊤ (s i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, pullbackFrameSections_pullbackGlobalSections, smul_eq_mul]

/-- **The local equation of a linear combination of pulled-back sections.** On an affine `X`
the zero scheme of `∑ᵢ cᵢ · f^* sᵢ` is cut out by the function `∑ᵢ cᵢ · f^# aᵢ`, where `aᵢ` is
the function representing `sᵢ` under the trivialization of `M`. -/
theorem zeroScheme_ideal_top_sum_smul [IsAffine X]
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (c : ι → Γ(X, ⊤)) (s : ι → Γ(M, ⊤)) :
    (zeroScheme X ((Scheme.Modules.pullback f).obj M)
        (∑ i, c i • pullbackGlobalSections f M (s i))).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.span {∑ i, c i * f.appTop (e.hom.app ⊤ (s i))} := by
  refine AlgebraicGeometry.zeroScheme_ideal_of_trivialization X
    ((Scheme.Modules.pullback f).obj M) (∑ i, c i • pullbackGlobalSections f M (s i))
    ⟨⊤, isAffineOpen_top X⟩ (pullbackFrameSections f M e)
    (∑ i, c i * f.appTop (e.hom.app ⊤ (s i))) ?_
  have hid : ∀ t : Γ((Scheme.Modules.pullback f).obj M, ⊤),
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op t = t := by
    intro t
    simp
  rw [hid]
  exact pullbackFrameSections_sum_smul f M e c s

end LinearCombination

end Stacks.Divisors

end
