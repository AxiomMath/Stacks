module

public import StacksFrontier.AlgebraicGeometry.ProductFamilyRatio.Consequences
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 01VS: an ample invertible sheaf embeds a finite-type morphism in projective space

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `L` be an ample invertible
`𝒪_X`-module. Then there is a `d₀ ≥ 1` such that for every `d ≥ d₀` there are an `n` and an
immersion `i : X ⟶ ℙⁿ_S` over `S` with `L ^⊗ d ≅ i ^* 𝒪(1)`. This is [Stacks, Tag 01VS].

The reduction of the tag to named conditions, and the discharge of all but one of them, is
`StacksFrontier/AlgebraicGeometry/ProductFamilyRatio/Consequences.lean`; the condition left standing
there is `Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers L`, which asks for a finite
family of global sections generating every stalk of `L ^⊗ d` in every sufficiently positive degree
`d`. That is clause (7) of [Stacks, Tag 01Q3] at `F = 𝒪_X`, and it is available from ampleness as
`Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple` — but in the epimorphism form
`Stacks.AmpleEventualGeneration.IsFinGen`. `StalkwiseGeneration/Basic.lean` converts that form
into the stalkwise one, so the condition becomes a theorem and the tag follows with no hypothesis
beyond ampleness and finite type.

## Main results

* `Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple`: **clause (7) of
  [Stacks, Tag 01Q3] at `F = 𝒪_X`, in the stalkwise form**, from ampleness alone.
* `Stacks.StalkwiseGeneration.immersionTwistGap_of_isAmple`:
  `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`, from ampleness alone.
* `Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`: **[Stacks, Tag
  01VS]**, unconditionally.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.StalkwiseGeneration

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-- **Every sufficiently high tensor power of an ample invertible module carries a finite family
of global sections generating every stalk.** This is clause (7) of [Stacks, Tag 01Q3] at
`F = 𝒪_X`, in the generation predicate the morphism of [Stacks, Tag 01NE] is built from. The
epimorphism form is `Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`, and
`Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen` passes between the two forms. -/
@[ega "II 4.5.8" "special case"]
theorem eventuallyGeneratesStalksPowers_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers L := by
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple L hL
  exact ⟨n₀, fun d hd => exists_generatesStalks_of_isFinGen (hn₀ d hd)⟩

/-- **`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` from ampleness alone.** -/
theorem immersionTwistGap_of_isAmple {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    ImmersionTwistGap f L (tensorPowModule X L) :=
  Stacks.ProductFamilyRatio.immersionTwistGap_of_eventuallyGeneratesStalksPowers f L
    (eventuallyGeneratesStalksPowers_of_isAmple L hL)

/-- **[Stacks, Tag 01VS].** For `f : X ⟶ S` locally of finite type and `L` an ample invertible
`𝒪_X`-module there is a `d₀ ≥ 1` such that every degree `d ≥ d₀` admits an immersion
`i : X ⟶ ℙⁿ_S` over `S` pulling the twisting sheaf `𝒪(1)` back to `L ^⊗ d`. -/
@[stacks 01VS]
theorem exists_immersion_projectiveSpaceOver_of_isAmple {S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) [LocallyOfFiniteType f] :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  Stacks.ProductFamilyRatio.exists_immersion_projectiveSpaceOver_of_isAmple f L hL
    (eventuallyGeneratesStalksPowers_of_isAmple L hL)

end Stacks.StalkwiseGeneration

end
