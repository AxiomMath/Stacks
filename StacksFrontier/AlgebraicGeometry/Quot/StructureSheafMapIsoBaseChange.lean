module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequencePairKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel

/-!
# The hypothesis of Stacks 0D27 is stable under base change

For a morphism `f : X ⟶ Y` of algebraic spaces, the condition that `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every scheme `T` over `Y`
(`AlgebraicGeometry.Space.PicardSituation.StructureSheafMapIso`, the hypothesis of Stacks 0D27
and 0D2C) passes to every base change `X ×_Y Y' ⟶ Y'`: a scheme over
`Y'` is a scheme over `Y`, and the two base changes agree up to an isomorphism over it.  The proof
of Stacks 0D2C uses this for the base change along `f` itself.  Nothing here carries a `@[stacks]`
attribute.

## Main results

* `AlgebraicGeometry.Space.isIso_structureSharp_of_isIso`: the structure map of an isomorphism of
  algebraic spaces is an isomorphism (it is a split monomorphism, and an epimorphism since an
  isomorphism is a closed immersion).
* `AlgebraicGeometry.Space.isIso_structureSharp_comp_iff`: precomposing with an isomorphism does
  not change whether a structure map is an isomorphism.
* `AlgebraicGeometry.Space.CoherentSituation.structureSheafMapIso_baseChange`.

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure map `e♯ : 𝒪_Y ⟶ e_*𝒪_X` of an isomorphism `e` of algebraic spaces is an
isomorphism. -/
theorem isIso_structureSharp_of_isIso {X Y : AlgebraicSpaces B S hS} (e : X ⟶ Y) [IsIso e] :
    IsIso (structureSharp B S hS e) := by
  obtain ⟨r, hr⟩ := exists_structureSharp_comp_eq_id B S hS e
  have : IsIso e.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map e))
  have : Epi (structureSharp B S hS e) :=
    epi_structureSharp B S hS e (isClosedImmersion_of_isIso B S hS e.hom)
  refine ⟨r, hr, ?_⟩
  rw [← cancel_epi (structureSharp B S hS e), reassoc_of% hr, Category.comp_id]

/-- **The structure map of a morphism is an isomorphism exactly when that of its precomposite
with an isomorphism is**: `(e ≫ q)♯ = q♯ ≫ q_*(e♯)` up to the comparison of iterated direct
images, and `e♯` is an isomorphism. -/
theorem isIso_structureSharp_comp_iff {X' X T : AlgebraicSpaces B S hS} (e : X' ⟶ X) [IsIso e]
    (q : X ⟶ T) :
    IsIso (structureSharp B S hS (e ≫ q)) ↔ IsIso (structureSharp B S hS q) := by
  have := isIso_structureSharp_of_isIso e
  have hc : IsIso (pushforwardRingSheafCompHom B S hS e q (structureRingSheaf B S hS X')) :=
    ⟨pushforwardRingSheafCompInv B S hS e q _, pushforwardRingSheafCompHom_comp_inv B S hS e q _,
      pushforwardRingSheafCompInv_comp_hom B S hS e q _⟩
  have h₁ : IsIso ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
      (structureSharp B S hS e)) := Functor.map_isIso _ _
  have h₂ : IsIso ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
      (structureSharp B S hS e) ≫
        pushforwardRingSheafCompHom B S hS e q (structureRingSheaf B S hS X')) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ hc
  rw [← structureSharp_comp_pushforwardRingSheafCompHom B S hS e q]
  exact ⟨fun h ↦ @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ h,
    fun h ↦ @IsIso.comp_isIso _ _ _ _ _ _ _ h h₂⟩

/-- **The hypothesis of Stacks 0D27 is stable under base change.**  If `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is
an isomorphism for every scheme `T` over `Y`, then the same holds for the base change
`X ×_Y Y' ⟶ Y'` along any `g : Y' ⟶ Y`: its base change to a scheme `T` over `Y'` is the base
change of `f` to `T` read over `Y`. -/
theorem CoherentSituation.structureSheafMapIso_baseChange (D : CoherentSituation B S hS)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y)
    (hstr : D.toPicardSituation.StructureSheafMapIso) :
    (D.baseChange g).toPicardSituation.StructureSheafMapIso := fun T ↦ by
  show IsIso (structureSharp B S hS (baseChangeInclusion (D.baseChange g).f T))
  rw [← D.baseChangeSpaceIso_hom_inclusion g T, isIso_structureSharp_comp_iff]
  exact hstr ((D.overBase g).obj T)

end AlgebraicGeometry.Space

end
