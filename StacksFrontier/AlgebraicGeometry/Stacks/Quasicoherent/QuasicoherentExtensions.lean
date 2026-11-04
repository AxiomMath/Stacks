module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRestrictionRightExactAll
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSiteAgreement

/-!
# Extensions of quasi-coherent modules on a category fibred in groupoids

Let `𝒳` be a category fibred in groupoids over `(Sch/S)_fppf`, for instance an algebraic stack,
and let `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` be a short exact sequence
in `Mod(𝒪_𝒳)` with `𝓕₁` and `𝓕₃` quasi-coherent.  Then `𝓕₂` is quasi-coherent.

The proof is the source's.  Quasi-coherence of a module on `𝒳` may be checked after restriction
to the localizations `𝒳_fppf/x ≅ (Sch/U)_fppf`, one for each object `x` lying over a scheme `U`
(Stacks 06WI).  Restriction to a localized site is exact on module sheaves, so the restricted
sequence is a short exact sequence on the big fppf site of `U` with quasi-coherent outer terms,
and there the middle term is quasi-coherent by Stacks 0GNC (4).

## Main results

* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_X₂_of_shortExact`: **Stacks 06WV (7)**,
  for every category fibred in groupoids over `(Sch/S)_fppf`, in particular for every algebraic
  stack.
* `AlgebraicGeometry.FibredSite.isClosedUnderExtensions_isQuasicoherentOnSite`: the same, as
  closure of quasi-coherence under extensions.

## Implementation notes

The source states the result for an algebraic stack; the proof uses nothing about `𝒳` beyond its
being fibred in groupoids over `(Sch/S)_fppf`, and it is stated in that generality.  The slices
`𝒳/x` are essentially small, which is what makes the module categories involved abelian.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

/-- **Stacks 06WV (7).**  Let `𝒳` be a category fibred in groupoids over `(Sch/S)_fppf`, for
instance an algebraic stack, and let `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` be a short exact sequence in
`Mod(𝒪_𝒳)` with `𝓕₁` and `𝓕₃` quasi-coherent.  Then `𝓕₂` is quasi-coherent.

By Stacks 06WI it suffices that `x^*𝓕₂` be quasi-coherent on `(Sch/U)_fppf` for each object `x`
over a scheme `U`.  The functor `x^*` is restriction to `𝒳_fppf/x` followed by an equivalence;
restriction to a localized site is exact (Stacks 03DA), so `x^*` carries the sequence to a short
exact sequence on `(Sch/U)_fppf`, whose middle term is quasi-coherent by Stacks 0GNC (4),
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`. -/
@[stacks 06WV "part (7): an extension in Mod(𝒪_𝒳) of quasi-coherent modules is quasi-coherent, \
  for every category fibred in groupoids over (Sch/S)_fppf, in particular for every algebraic \
  stack"]
theorem isQuasicoherentOnSite_X₂_of_shortExact
    {C : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    C.X₂.IsQuasicoherentOnSite := by
  have := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp .fppf
  have := (have : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS p .fppf))
  rw [isQuasicoherentOnSite_iff_forall_objectInverseImage] at h₁ h₃ ⊢
  intro x
  have := essentiallySmall_over B S hS p hp x
  have := hasSheafifyEssentiallySmallSite
    ((BigFppfOver.associatedTopology B S hS p .fppf).over x) AddCommGrpCat.{u}
  have := wEqualsLocallyBijective_over B S hS p hp .fppf x
  have : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits x
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u, u} x
  exact BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all (τ := .fppf)
    (hC.map_of_exact (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x ⋙
      (localizationModulesEquivalence B S hS p hp x).inverse)) (h₁ x) (h₃ x)

variable (B S hS p hp) in
/-- Quasi-coherence of modules on the fppf site of a category fibred in groupoids over
`(Sch/S)_fppf` is closed under extensions. -/
instance isClosedUnderExtensions_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hC h₁ h₃ := isQuasicoherentOnSite_X₂_of_shortExact hC h₁ h₃

end AlgebraicGeometry.FibredSite

end
