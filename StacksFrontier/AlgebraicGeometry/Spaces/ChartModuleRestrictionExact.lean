module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# Exactness and conservativity for the restrictions of a module on an algebraic space

A chartwise argument about `𝒪_F`-modules on an algebraic space `F` consumes two things about
the restriction of a module to a chart: that the restriction is exact enough to carry kernels
and cokernels along, and that a morphism which every restriction in a covering family turns
into an isomorphism was already an isomorphism.  This file supplies both, for the two
restrictions the small étale site offers, and records which half of exactness each one has.

## Main results

* `Stacks.PresheafOfModules.preservesFiniteLimits_pushforward` — the pushforward of presheaves
  of modules along *any* functor of the underlying categories, with any change of scalars, is
  left exact: on underlying presheaves of abelian groups it is precomposition, and finite
  limits of presheaves of modules are computed on those.
* `AlgebraicGeometry.Space.preservesFiniteLimits_restrictToChartSchemeFunctor` — **restriction
  of an `𝒪_F`-module to the scheme underlying an étale chart is left exact**, and
  `AlgebraicGeometry.Space.restrictToChartSchemeKernelIso` is the resulting identification of
  the restriction of a kernel with the kernel of the restriction.
* `Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map` — **restriction to the slices at the
  members of a family of objects covering the final object is a jointly conservative family of
  functors**, and `AlgebraicGeometry.Space.isIso_of_isIso_over_of_isSurjective` is its form for
  one étale chart of an algebraic space whose structure morphism is surjective.

## Implementation notes

### Which restriction has which half of exactness

There are two restrictions of an `𝒪_F`-module along an étale chart `U`, and they behave
differently.

*Restriction to the slice* of the small étale site at `U` is `SheafOfModules.overFunctor`.  It
is **exact**, which is `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`
and `...overFunctor_preservesFiniteColimits`, and by the result below it is **jointly
conservative** over a covering family.  It is the restriction along which a question about
`𝒪_F`-modules is genuinely local.  What it does not do is land in the scheme-level categories:
its target is the modules on the small étale site of `U`, not the Zariski modules
`(chartScheme U).Modules` that the scheme-level theory is stated for.

*Restriction to the scheme underlying `U`* is `AlgebraicGeometry.Space.restrictToChartScheme`,
whose target is `(chartScheme U).Modules`.  It is **left exact** — the content of this file —
but it is not right exact and should not be expected to be: forgetting the sections over
charts which are not Zariski opens makes it the pushforward along the morphism of sites
`U_étale ⟶ U_Zariski`, that is, a right adjoint.  For the same reason it is not jointly
conservative over a covering family of charts: its value at `U` sees only the Zariski opens of
`U`, while a chart over a member of a covering family need not be one of those, so bijectivity
of the sections on a covering family of charts is not what it delivers.

### Left exactness of the restriction to the chart scheme

`AlgebraicGeometry.Space.restrictToChartSchemeFunctor` is a composite of four functors, and
each of them is left exact for its own reason: the universe lift of the sections is
`SheafOfModules.uliftForPresentationFunctor_preservesFiniteLimits`, the forgetful functor to
presheaves of modules is `SheafOfModules.forgetPreservesFiniteLimits`, the pushforward is
`Stacks.PresheafOfModules.preservesFiniteLimits_pushforward` below, and Zariski sheafification
is `PresheafOfModules.instPreservesFiniteLimitsSheafification`.  The proof therefore only has
to reinstate the two sheafification instances that the definition of the functor carries
inside its body, and compose.  The forgetful functor's instances are also supplied by name:
instance search does not find Mathlib's instances on `SheafOfModules.forget` at the ring sheaf
`Stacks.SheafOfModules.Tensor.ringSheaf` of the small étale site, although they apply.

### Joint conservativity

`CategoryTheory.Sheaf.isIso_of_coversTop` is the same statement for sheaves with values in an
arbitrary category, phrased with `GrothendieckTopology.overPullback`.  Both the restriction of
a sheaf of modules to a slice and that functor are precomposition with `(Over.forget U).op` on
the underlying presheaf of abelian groups, so the two restricted morphisms are *equal*, and
the reduction is one application of `CategoryTheory.isIso_of_reflects_iso` along
`SheafOfModules.toSheaf`, which reflects isomorphisms.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂ u m

/-! ### Left exactness of the pushforward of presheaves of modules -/

namespace Stacks.PresheafOfModules

/-- **The pushforward of presheaves of modules is left exact.**  For a functor `G : C ⥤ D` and a
morphism of presheaves of rings `φ : S ⟶ G.op ⋙ R`, the induced functor on presheaves of
modules is precomposition with `G.op` on the underlying presheaves of abelian groups, where
precomposition preserves all limits; finite limits of presheaves of modules are both preserved
and reflected by the passage to those underlying presheaves. -/
theorem preservesFiniteLimits_pushforward {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {G : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ G.op ⋙ R) :
    PreservesFiniteLimits (_root_.PresheafOfModules.pushforward.{w} φ) := by
  have h₁ : PreservesFiniteLimits (_root_.PresheafOfModules.toPresheaf.{w} R ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ _).obj G.op) :=
    Limits.comp_preservesFiniteLimits _ _
  have h₂ : PreservesFiniteLimits
      (_root_.PresheafOfModules.pushforward.{w} φ ⋙ _root_.PresheafOfModules.toPresheaf S) :=
    Limits.preservesFiniteLimits_of_natIso
      (_root_.PresheafOfModules.pushforwardCompToPresheaf φ).symm
  exact ⟨fun _ _ _ => Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (_root_.PresheafOfModules.toPresheaf S)⟩

/-- The pushforward of presheaves of modules sends the zero morphism to the zero morphism: on
sections it is the given morphism read at another object of the site. -/
theorem preservesZeroMorphisms_pushforward {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {G : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ G.op ⋙ R) :
    (_root_.PresheafOfModules.pushforward.{w} φ).PreservesZeroMorphisms where
  map_zero M N := by
    ext X x
    rfl

end Stacks.PresheafOfModules

/-! ### Joint conservativity of the restrictions to the slices at a covering family -/

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}

/-- **Restriction to the slices at the members of a family of objects which covers the final
object is a jointly conservative family of functors.**  A morphism of sheaves of modules whose
restriction to the slice at every `V i` is an isomorphism is an isomorphism.

On underlying presheaves of abelian groups the restriction to the slice at `V i` is
precomposition with `(Over.forget (V i)).op`, which is also what
`CategoryTheory.GrothendieckTopology.overPullback` is; the hypothesis therefore says exactly
that the underlying morphism of abelian sheaves becomes invertible on the covering family, and
`CategoryTheory.Sheaf.isIso_of_coversTop` concludes for it.  `SheafOfModules.toSheaf` reflects
isomorphisms, so the morphism of sheaves of modules is itself invertible. -/
theorem isIso_of_isIso_overFunctor_map {ι : Type*} {V : ι → C}
    (hV : J.CoversTop V) {A B : _root_.SheafOfModules.{w} R} (f : A ⟶ B)
    (hf : ∀ i, IsIso ((_root_.SheafOfModules.overFunctor.{w} R (V i)).map f)) : IsIso f := by
  have h : IsIso ((_root_.SheafOfModules.toSheaf.{w} R).map f) := by
    refine Sheaf.isIso_of_coversTop hV fun i => ?_
    have := hf i
    exact inferInstanceAs (IsIso ((_root_.SheafOfModules.toSheaf.{w} (R.over (V i))).map
      ((_root_.SheafOfModules.overFunctor.{w} R (V i)).map f)))
  exact isIso_of_reflects_iso f (_root_.SheafOfModules.toSheaf.{w} R)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **One surjective étale chart detects isomorphisms of `𝒪_F`-modules.**  A morphism of
`𝒪_F`-modules whose restriction to the slice of the small étale site at a chart with surjective
structure morphism is an isomorphism is an isomorphism.

Such a chart covers the final object of the small étale site
(`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`), and restriction to the slices
at a covering family is jointly conservative. -/
theorem isIso_of_isIso_over_of_isSurjective (U : SmallEtale B S hS F)
    (hU : IsSurjective B S hS U.1.hom) {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N)
    (hf : IsIso ((SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).map f)) :
    IsIso f :=
  Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map
    (SmallEtale.coversTop_of_isSurjective B S hS F hF U hU) f fun _ => hf

/-! ### Left exactness of the restriction to an étale chart's scheme -/

/-- **Restriction of an `𝒪_F`-module to the scheme underlying an étale chart is left exact.**

The functor is a composite of four left exact ones: the universe lift of the sections, the
forgetful functor to presheaves of modules, the pushforward along the inclusion of the Zariski
opens of the chart as étale charts of `F`, and Zariski sheafification.  Right exactness does
not hold and is not claimed; see the implementation notes of this file. -/
theorem preservesFiniteLimits_restrictToChartSchemeFunctor (U : SmallEtale B S hS F) :
    PreservesFiniteLimits (restrictToChartSchemeFunctor.{u, m} B S hS F hF U) := by
  let _ : HasSheafify (Opens.grothendieckTopology (chartScheme U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  let _ : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := SheafOfModules.Finite.forgetPreservesFiniteLimits.{max u m}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  have := Stacks.PresheafOfModules.preservesFiniteLimits_pushforward.{max u m}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj)
    (chartSchemeRestrictionRingHom B S hS F U)
  have h₃ : PreservesFiniteLimits
      (PresheafOfModules.pushforward.{max u m}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O).obj)
          (chartSchemeRestrictionRingHom B S hS F U) ⋙
        PresheafOfModules.sheafification.{max u m} (𝟙 (chartScheme U).ringCatSheaf.obj)) :=
    Limits.comp_preservesFiniteLimits _ _
  have h₂ : PreservesFiniteLimits
      (SheafOfModules.forget.{max u m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        PresheafOfModules.pushforward.{max u m}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O).obj)
          (chartSchemeRestrictionRingHom B S hS F U) ⋙
        PresheafOfModules.sheafification.{max u m} (𝟙 (chartScheme U).ringCatSheaf.obj)) :=
    Limits.comp_preservesFiniteLimits _ _
  have h₁ : PreservesFiniteLimits
      (SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, m, u}
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        SheafOfModules.forget.{max u m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        PresheafOfModules.pushforward.{max u m}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O).obj)
          (chartSchemeRestrictionRingHom B S hS F U) ⋙
        PresheafOfModules.sheafification.{max u m} (𝟙 (chartScheme U).ringCatSheaf.obj)) :=
    Limits.comp_preservesFiniteLimits _ _
  exact h₁

/-- Restriction of an `𝒪_F`-module to the scheme underlying an étale chart sends the zero
morphism to the zero morphism, each of its four steps doing so. -/
theorem preservesZeroMorphisms_restrictToChartSchemeFunctor (U : SmallEtale B S hS F) :
    (restrictToChartSchemeFunctor.{u, m} B S hS F hF U).PreservesZeroMorphisms := by
  let _ : HasSheafify (Opens.grothendieckTopology (chartScheme U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  let _ : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : (SheafOfModules.forget.{max u m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget _
  have := Stacks.PresheafOfModules.preservesZeroMorphisms_pushforward.{max u m}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj)
    (chartSchemeRestrictionRingHom B S hS F U)
  have h : (SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, m, u}
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        SheafOfModules.forget.{max u m}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        PresheafOfModules.pushforward.{max u m}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O).obj)
          (chartSchemeRestrictionRingHom B S hS F U) ⋙
        PresheafOfModules.sheafification.{max u m}
          (𝟙 (chartScheme U).ringCatSheaf.obj)).PreservesZeroMorphisms :=
    inferInstance
  exact h

/-- Restriction to an étale chart's scheme carries the kernel of a morphism of `𝒪_F`-modules to
the kernel of its restriction, by
`AlgebraicGeometry.Space.preservesFiniteLimits_restrictToChartSchemeFunctor`. -/
def restrictToChartSchemeKernelIso (U : SmallEtale B S hS F)
    {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N) :
    restrictToChartScheme B S hS F hF (kernel f) U ≅
      kernel ((restrictToChartSchemeFunctor B S hS F hF U).map f) :=
  have := preservesFiniteLimits_restrictToChartSchemeFunctor B S hS F hF U
  have := preservesZeroMorphisms_restrictToChartSchemeFunctor B S hS F hF U
  PreservesKernel.iso (restrictToChartSchemeFunctor B S hS F hF U) f

end AlgebraicGeometry.Space

end
