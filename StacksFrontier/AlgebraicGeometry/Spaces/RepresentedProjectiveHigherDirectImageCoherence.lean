module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoherentColimit
public import StacksFrontier.AlgebraicGeometry.LocallyProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageComparison

/-!
# Coherence of the higher direct images along a projective morphism of represented spaces

Let `ψ : Z ⟶ T` be a morphism of the big fppf site over `S` whose underlying morphism of schemes
is projective, with `T` locally Noetherian, and let `𝓜` be a coherent `𝒪_Z`-module. Then every
higher direct image `R ᵏ (h_ψ)_* (𝓜^a)` along the morphism of represented algebraic spaces
`h_ψ = yoneda.map ψ` is a coherent module on `h_T`.

This is the input of the proof of Stacks 08AR that the source cites as Cohomology of Schemes,
Lemma 30.19.2 (Stacks 02O4): by Stacks 071N, here in its separated case
`AlgebraicGeometry.Space.nonempty_rightDerived_modulePushforward_representedSpaceMap_iso`, the
higher direct image is the associated module of the higher direct image of schemes, which is
coherent by Stacks 02O4, and the associated module of a coherent module on a locally Noetherian
scheme is coherent on the represented algebraic space.

## Main results

* `AlgebraicGeometry.Space.isCoherent_representedAssociatedModule`: `𝓜^a` is coherent for a
  coherent `𝓜` on a locally Noetherian scheme of the site.
* `AlgebraicGeometry.Space.hasCoherentHigherDirectImages_representedSpaceMap`: the higher direct
  images of `𝓜^a` along `h_ψ` are coherent, for `ψ` projective.

## References

* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The associated module of a coherent module is coherent.** For a coherent module `𝓜` on a
locally Noetherian scheme underlying an object `U` of the site, `𝓜^a` is a coherent module on the
represented algebraic space `h_U`: it is quasi-coherent, and of finite type because `𝓜` is. -/
theorem isCoherent_representedAssociatedModule (U : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hM : M.IsCoherent) :
    IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj M) := by
  have : Fact (HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_of_representable B S hS _ _ U (Iso.refl _) inferInstance⟩
  have hq : M.IsQuasicoherent := GroupoidScheme.isQuasicoherent_of_isCoherent M hM
  have hft : M.IsFiniteType := Stacks.Chow.isFiniteType_of_isCoherent M
  refine (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS _ _ _).2
    ⟨isQuasicoherentOnSite_representedAssociatedModule B S hS U _ M hq, ?_⟩
  exact Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _
    (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS U M hq hft)

/-- **Stacks 02O4 on represented algebraic spaces.** Let `ψ : Z ⟶ T` be a morphism of the site
whose underlying morphism of schemes is projective, with `T` locally Noetherian, and let `𝓜` be a
coherent `𝒪_Z`-module. Then every `R ᵏ (h_ψ)_* (𝓜^a)` is coherent. -/
theorem hasCoherentHigherDirectImages_representedSpaceMap {Z T : BigFppfOver B S hS} (ψ : Z ⟶ T)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (hψ : IsProjectiveMorphism ((BigFppfOver.toScheme B S hS).map ψ))
    (M : ((BigFppfOver.toScheme B S hS).obj Z).Modules) (hM : M.IsCoherent) :
    HasCoherentHigherDirectImages B S hS (representedSpaceMap B S hS ψ)
      ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj M) := by
  intro k
  have hp := isProper_of_isProjectiveMorphism _ hψ
  obtain ⟨e⟩ := nonempty_rightDerived_modulePushforward_representedSpaceMap_iso B S hS ψ
    inferInstance inferInstance M (GroupoidScheme.isQuasicoherent_of_isCoherent M hM) k
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
  exact isCoherent_of_iso B S hS _ e.symm
    (isCoherent_representedAssociatedModule B S hS T _
      (LocallyProjectiveCoherentImage.isCoherent_rightDerived_of_isProjectiveMorphism _ hψ M hM k))

end AlgebraicGeometry.Space

end
