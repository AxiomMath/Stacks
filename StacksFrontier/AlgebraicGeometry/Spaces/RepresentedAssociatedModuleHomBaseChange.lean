module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackNaturality

/-!
# The identification of morphisms of associated modules with linear maps is a base change

For an object `T` of the big fppf site over `S` whose underlying scheme is affine and
quasi-coherent `𝒪`-modules `M`, `N` on that scheme,
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap` identifies the morphisms
`Mᵃ ⟶ Nᵃ` of `𝒪`-modules on the small étale site of `yoneda.obj T` with the `Γ(T, ⊤)`-linear maps
`Γ(M, ⊤) ⟶ Γ(N, ⊤)`.  This file proves that the identification commutes with base change along a
morphism `g : T' ⟶ T` of the site: the linear map attached to the inverse image of a morphism of
associated modules is the base change of the linear map attached to it.

This is one of the four compatibilities that a *naturality in the chart* of the identification of
a chart-level section of an internal Hom with a Zariski linear map needs — the one on the Zariski
side — and it is the one whose inputs are all available.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_map`: **the characterising
  equation.**  The linear map attached to `βᵃ` is `β` on global sections.  This is the only way
  the identification can be used: its first factor is the inverse of `β ↦ βᵃ`, an
  `Equiv.ofBijective` and hence a `Function.surjInv`, so no value of it can be computed, but every
  morphism of associated modules *is* a `βᵃ`.
* `AlgebraicGeometry.Space.associatedModule_map_pullback`: the inverse image along a represented
  morphism of `βᵃ`, conjugated by the transport of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, is the associated morphism of
  the Zariski pullback of `β`.
* `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_pullbackSection`: **the
  identification commutes with base change.**  The linear map attached to the inverse image of
  `χ : Mᵃ ⟶ Nᵃ` carries the pullback of a global section of `M` to the pullback of the image of
  that section under the linear map attached to `χ`.

## Implementation notes

The proof is the only one available: a morphism of associated modules into a quasi-coherent target
is `βᵃ` for a unique Zariski `β`
(`AlgebraicGeometry.Space.bijective_representedAssociatedModule_map`, the small étale half of
[Stacks Project, Tag 0GN7]), both sides of the statement are computed at `βᵃ` through the
characterising equation, and what remains is the naturality of the unit of `g^* ⊣ g_*` on global
sections, `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`.  **No value of the
`Function.surjInv` is ever computed.**

The conjugation is stated with
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, whose naturality in the Zariski
module is proved; the two spellings
`(representedSmallEtaleModuleEquivalence B S hS T).functor.obj`
of `((SmallEtale.associatedModule …).obj M)` and `(representedAssociatedModule B S hS T hT).obj M`
are the same term, by
`AlgebraicGeometry.Space.representedAssociatedModule_eq_comp`, so no transport appears.

No `@[stacks]` attribute is claimed: Tag 0GN7 is registered where the bijection is proved and
Tag 03LC (1) where the base-change comparison is built; what is proved here is their
compatibility.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The characterising equation of the identification of morphisms of associated modules with
linear maps of global sections.**  The linear map attached to `βᵃ` is `β` read on global
sections.

This is how the identification has to be used.  Its first factor is the inverse of `β ↦ βᵃ`, an
`Equiv.ofBijective` and hence a `Function.surjInv`, so the composite cannot describe its own
values; but `β ↦ βᵃ` is surjective, so every morphism of associated modules is a `βᵃ` and this
equation determines the identification everywhere. -/
theorem representedAssociatedModuleHomEquivLinearMap_map (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M N : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (β : M ⟶ N) :
    representedAssociatedModuleHomEquivLinearMap B S hS U hF M N
        ((representedAssociatedModule B S hS U hF).map β) =
      Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ β :=
  congrArg Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ
    ((Equiv.ofBijective _
      (bijective_representedAssociatedModule_map B S hS U hF M N)).symm_apply_apply β)

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The inverse image of `βᵃ` is the associated morphism of the Zariski pullback of `β`.**
Conjugating the inverse image along the represented morphism by the transport of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` turns `βᵃ` into `(g^*β)ᵃ`.

This is `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality` with the
left-hand comparison cancelled. -/
theorem associatedModule_map_pullback
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T'))
    {M N : ((BigFppfOver.toScheme B S hS).obj T).Modules} (β : M ⟶ N) :
    (representedAssociatedModulePullbackIso B S hS g hg M).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS g)).map
            ((representedAssociatedModule B S hS T hT).map β) ≫
          (representedAssociatedModulePullbackIso B S hS g hg N).hom =
      (representedAssociatedModule B S hS T' hT').map
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map β) :=
  (congrArg (fun z => (representedAssociatedModulePullbackIso B S hS g hg M).inv ≫ z)
      (representedAssociatedModulePullbackIso_naturality B S hS g hg β)).trans
    (Iso.inv_hom_id_assoc _ _)

/-- **The identification of morphisms of associated modules with linear maps of global sections
commutes with base change.**  For `g : T' ⟶ T` a morphism of the big fppf site with both
underlying schemes affine, and `χ : Mᵃ ⟶ Nᵃ` a morphism of associated modules of quasi-coherent
Zariski modules on the scheme of `T`, the linear map attached to the inverse image of `χ` carries
the pullback of a global section of `M` to the pullback of its image under the linear map attached
to `χ`.

This is the Zariski-side compatibility that a naturality in the chart of the identification of a
chart-level section of an internal Hom with a Zariski linear map needs. -/
theorem representedAssociatedModuleHomEquivLinearMap_pullbackSection
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T'))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (M N : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (χ : (representedAssociatedModule B S hS T hT).obj M ⟶
      (representedAssociatedModule B S hS T hT).obj N)
    (x : Γ(M, (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens))) :
    representedAssociatedModuleHomEquivLinearMap B S hS T' hT'
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M)
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj N)
        ((representedAssociatedModulePullbackIso B S hS g hg M).inv ≫
          (modulePullback B S hS (representedSpaceMap B S hS g)).map χ ≫
            (representedAssociatedModulePullbackIso B S hS g hg N).hom)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map g) M ⊤ ⊤ le_top x) =
      Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map g) N ⊤ ⊤ le_top
        (representedAssociatedModuleHomEquivLinearMap B S hS T hT M N χ x) := by
  obtain ⟨β, hβ⟩ := (bijective_representedAssociatedModule_map B S hS T hT M N).2 χ
  have hβ' : (representedAssociatedModule B S hS T hT).map β = χ := hβ
  subst hβ'
  refine Eq.trans (congrArg (fun z => representedAssociatedModuleHomEquivLinearMap B S hS T' hT'
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M)
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj N) z
      (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map g) M ⊤ ⊤ le_top x))
    (associatedModule_map_pullback B S hS g hg hT hT' β)) ?_
  rw [representedAssociatedModuleHomEquivLinearMap_map,
    representedAssociatedModuleHomEquivLinearMap_map]
  exact Scheme.Modules.pullbackSection_naturality ((BigFppfOver.toScheme B S hS).map g) β ⊤ ⊤
    le_top x

end AlgebraicGeometry.Space

end
