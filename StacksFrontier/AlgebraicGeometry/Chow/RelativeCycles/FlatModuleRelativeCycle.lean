module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleGeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The family of cycles of a module flat over the base is a relative cycle

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let `F` be
a quasi-coherent `𝒪_X`-module of finite type whose support meets every fibre of `f` in dimension
at most `r`. If `F` is flat over `S`, then the family `[F/X/S]_r` of `r`-cycles on the fibres of
`X/S` is a relative `r`-cycle.

The valuative condition defining a relative `r`-cycle is tested after base change along a
morphism `g : Spec R ⟶ S` with `R` a discrete valuation ring. Base change carries `[F/X/S]_r` to
the family of the pulled-back module and carries flatness over the base with it, so the condition
to be checked is the specialization formula over a discrete valuation ring for a flat module,
which is Stacks 0H4I.

## Main results

* `Stacks.Chow.isRelativeCycle_familyAssociatedToModule_of_isFlatOver` — the family of cycles of
  a module flat over the base is a relative cycle.

## Implementation notes

The two ingredients are `Stacks.Chow.familyAssociatedToModule_baseChange_general`, the base
change clause of Tag 0H4R along an arbitrary morphism of bases, and
`Stacks.Chow.specializationCycle_familyAssociatedToModule`, Tag 0H4I. Flatness over the base
travels along the base change by `AlgebraicGeometry.modulePullback_isFlatOver`, Tag 01U8.

The dimension bound that `Stacks.Chow.familyAssociatedToModule` takes as an argument is a
proposition, so the proof of it produced by the base change clause and the proof of it produced
by Tag 0H4I from the bound on the generic fibre are interchangeable; no transport is needed.

## References

* [Stacks Project, Lemma 0H56](https://stacks.math.columbia.edu/tag/0H56)
* [Stacks Project, Lemma 0H4I](https://stacks.math.columbia.edu/tag/0H4I)
* [Stacks Project, Lemma 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The family `[F/X/S]_r` of cycles on the fibres of `X/S` attached to a quasi-coherent module
`F` of finite type which is flat over `S` is a relative `r`-cycle.

The valuative condition is tested after base change along a morphism `Spec R ⟶ S` from the
spectrum of a discrete valuation ring. The base change of `[F/X/S]_r` is the family of the
pulled-back module, by the base change clause of Tag 0H4R along an arbitrary morphism of bases,
and the pulled-back module is again flat over the new base; so the identity to be checked is the
specialization formula of Tag 0H4I. -/
theorem isRelativeCycle_familyAssociatedToModule_of_isFlatOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (F : X.Modules) [F.IsFiniteType]
    [hFq : F.IsQuasicoherent] (r : ℕ)
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    IsRelativeCycle f r (familyAssociatedToModule f F r hdim) := by
  intro R _ _ _ g
  have hflat' : AlgebraicGeometry.IsFlatOver (pullback.snd f g).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) :=
    @modulePullback_isFlatOver _ _ _ _ f g (pullback.fst f g) (pullback.snd f g)
      (IsPullback.of_hasPullback f g) F hFq hflat
  rw [familyAssociatedToModule_baseChange_general f g F r hdim]
  exact specializationCycle_familyAssociatedToModule (pullback.snd f g)
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F) hflat' r
    (supportDimension_le_of_baseChange_general f g F r hdim
      (genericPoint (Spec (CommRingCat.of R))))

/-- **Stacks Project, Lemma 0H56.** The family `[F/X/S]_r` of cycles on the fibres of `X/S`
attached to a quasi-coherent module `F` of finite type which is flat over `S` in dimensions
`≥ r` is a relative `r`-cycle.

The valuative condition is tested after base change along a morphism `Spec R ⟶ S` from the
spectrum of a discrete valuation ring. Flatness over the base in dimensions `≥ r` survives that
base change (Tag 0CWF), the base change of `[F/X/S]_r` is the family of the pulled-back module
(the base change clause of Tag 0H4R), and over a discrete valuation ring the specialization
formula holds for a module flat over the base in dimensions `≥ r`. -/
theorem isRelativeCycle_familyAssociatedToModule_of_isFlatOverInDimensionsGE {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hF : AlgebraicGeometry.IsFlatOverInDimensionsGE f F r)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    IsRelativeCycle f r (familyAssociatedToModule f F r hdim) := by
  intro R _ _ _ g
  rw [familyAssociatedToModule_baseChange_general f g F r hdim]
  exact specializationCycle_familyAssociatedToModule_of_isFlatOverInDimensionsGE
    (pullback.snd f g) ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
    (hF.of_isPullback (IsPullback.of_hasPullback f g) F r)
    (supportDimension_le_of_baseChange_general f g F r hdim)

end Stacks.Chow

end
