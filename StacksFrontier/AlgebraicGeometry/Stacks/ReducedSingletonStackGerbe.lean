module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeInertiaCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfFlatInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaFieldSpectrumCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp

/-!
# A reduced locally Noetherian one-point algebraic stack is a gerbe (Stacks 06QK)

**Stacks 06QK** says that a reduced, locally Noetherian algebraic stack `𝒵` over `S` whose space
of points `|𝒵|` is a singleton is a gerbe over a reduced, locally Noetherian algebraic space `Z`
with `|Z|` a singleton.

The source argues as follows. **Stacks 06MP** (1) `⟹` (2) supplies a 1-morphism
`Spec k ⟶ 𝒵` from the spectrum of a field which is surjective, flat and locally of finite
presentation. Its base change of the inertia `I_𝒵 ⟶ 𝒵` is representable by algebraic spaces and
locally of finite type (**Stacks 04Z4**, **Stacks 06FS**), hence locally of finite presentation
because the base is the spectrum of a field, and flat for the same reason; so `I_𝒵 ⟶ 𝒵` is flat
and locally of finite presentation by the fppf descent of **Stacks 06PZ** and **Stacks 06Q8**,
and `𝒵` is a gerbe by **Stacks 06QJ** (2) `⟹` (1). Choosing `π : 𝒵 ⟶ Z` which exhibits `𝒵` as a
gerbe over an algebraic space, `π` is surjective, flat and locally of finite presentation by
**Stacks 06QI**, so the composite `Spec k ⟶ Z` is too, by **Stacks 04ZS**, **Stacks 06PX** and
**Stacks 06FT**; and then **Stacks 06MP** (2) `⟹` (1) makes `Z` reduced, locally Noetherian with
`|Z|` a singleton.

Each step is available in the library; the names below are in the namespace
`AlgebraicGeometry.Stack.AlgebraicStacks` unless stated otherwise.

* The field cover of **Stacks 06MP** (1) `⟹` (2) is
  `hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian`, in the namespace
  `AlgebraicGeometry.Stack`.
* The fppf-local flatness and local finite presentation of the inertia over that cover is
  `hasFlatLfpLocalInertia_of_fieldSpectrumCover`; their fppf descent gives the flatness and local
  finite presentation of `I_𝒵 ⟶ 𝒵`.
* **Stacks 06QJ** (2) `⟹` (1) is
  `isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection`.
* The flatness and local finite presentation of a gerbe 1-morphism (**Stacks 06QI**) is
  `isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`.
* The surjectivity of a gerbe 1-morphism, the three composition statements, and Stacks 06MP
  (2) `⟹` (1) finish the proof.

## Main results

* `exists_gerbeOver_reducedLocallyNoetherianWithUniquePoint`, in the namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`: **Stacks 06QK**.

## Implementation notes

The algebraic space `Z` appears as an algebraic stack which is representable by an algebraic
space (**Stacks 04SV**), which is how `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbe` states the
absolute gerbe condition of Stacks 06QC and keeps `π` an ordinary 1-morphism of algebraic stacks;
the three properties asserted of `Z` are then read off the same predicate
`AlgebraicGeometry.Stack.IsReducedLocallyNoetherianWithUniquePoint` as those assumed of `𝒵`,
namely reducedness in the sense of **Stacks 04YF**, local Noetherianity, and the point space of
**Stacks 04XG** being nonempty and a subsingleton.

Surjectivity of the composite is proved on points directly rather than through a general
composition lemma: `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_comp` turns the goal into
the composite of two surjections of sets.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04Z4](https://stacks.math.columbia.edu/tag/04Z4)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 06QK](https://stacks.math.columbia.edu/tag/06QK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06QK.** Let `𝒵` be a reduced, locally Noetherian algebraic stack over `S` whose
space of points is a singleton. Then there is an algebraic stack `Z` over `S` which is
representable by an algebraic space, a 1-morphism `π : 𝒵 ⟶ Z` making `𝒵` a gerbe over `Z`, and
`Z` is again reduced, locally Noetherian with a single point. -/
@[stacks 06QK "The field cover of Stacks 06MP (1) implies (2), the flatness and local finite \
presentation of the inertia and their fppf descent, Stacks 06QJ (2) implies (1), the gerbe \
1-morphism being surjective, flat and locally of finite presentation by Stacks 06QI, and the \
conclusion about the base by Stacks 06MP (2) implies (1) applied to the composite from the \
field spectrum"]
theorem exists_gerbeOver_reducedLocallyNoetherianWithUniquePoint
    (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒵 : Stack.IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒵) :
    ∃ Z : Stack.AlgebraicStacks.{u, w} B S hS,
      IsRepresentableByAlgebraicSpace B S hS Z.val ∧
        (∃ π : 𝒵 ⟶ Z, IsGerbeOver B S hS π) ∧
          Stack.IsReducedLocallyNoetherianWithUniquePoint B S hS Z := by
  have hcov :=
    Stack.hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian.{u, w}
      B S hS 𝒵 h𝒵
  have hloc := hasFlatLfpLocalInertia_of_fieldSpectrumCover.{u, w} B S hS 𝒵 hcov
  obtain ⟨Z, hZrep, π, hπ⟩ :=
    isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection.{u, w} B S hS 𝒵
      (isFlat_inertiaProjection_of_hasFlatLfpLocalInertia B S hS 𝒵 hloc)
      (isLocallyOfFinitePresentation_inertiaProjection_of_hasFlatLfpLocalInertia B S hS 𝒵 hloc)
  obtain ⟨F, c, hclfp, hcsurj, hcflat⟩ := hcov
  obtain ⟨hπflat, hπlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS π hπ
  refine ⟨Z, hZrep, ⟨π, hπ⟩,
    Stack.isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
      B S hS Z ⟨F, c ≫ π, isLocallyOfFinitePresentation_comp B S hS c π hclfp hπlfp, ?_,
        isFlat_comp B S hS c π hcflat hπflat⟩⟩
  rw [Stack.IsSurjective, AlgebraicStacks.pointsMap_comp]
  exact (Stack.isSurjective_of_isGerbeOver B S hS π hπ).comp hcsurj

end AlgebraicGeometry.Stack.AlgebraicStacks

end
