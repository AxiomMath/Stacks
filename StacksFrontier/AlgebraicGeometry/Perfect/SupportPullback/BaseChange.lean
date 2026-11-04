module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic

/-!
# Proper support of a module under base change

In a cartesian square of schemes, the pullback of a finite type module whose support is proper
over the base again has support proper over the new base.

## Main results

* `AlgebraicGeometry.isProperOver_supp_pullback`: properness of the pulled-back module's
  support.

## Implementation notes

Support is the closed stalkwise support of a finite type sheaf of modules. The source's
quasi-coherence hypothesis is unnecessary: finite type alone gives closed support and the
pullback-support equality. Local finite type and finite type of the two pullbacks are supplied
by base change and by `AlgebraicGeometry.SheafOfModules.pullback_isFiniteType`.

The support of the pullback is the inverse image of the support, by
`SheafOfModules.supp_pullback`, so the statement is the properness of a preimage of a closed
subset under base change, which is `AlgebraicGeometry.isProperOver_preimage_baseChange`.

## References

* [Stacks Project, Tag 0CYT](https://stacks.math.columbia.edu/tag/0CYT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In a cartesian square, base change preserves properness of the support
of a finite type module over the base. -/
@[stacks 0CYT]
theorem isProperOver_supp_pullback {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType]
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩) :
    letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
    letI : ((Scheme.Modules.pullback g').obj F).IsFiniteType :=
      SheafOfModules.pullback_isFiniteType g'.toLRSHom.toShHom F
    IsProperOver f'
      ⟨SheafOfModules.supp ((Scheme.Modules.pullback g').obj F),
        SheafOfModules.isClosed_supp _⟩ := by
  let : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
  let : ((Scheme.Modules.pullback g').obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType g'.toLRSHom.toShHom F
  convert isProperOver_preimage_baseChange g' f' f g h
    ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩ hF using 1
  ext x
  simp [SheafOfModules.supp_pullback]

end AlgebraicGeometry

end
