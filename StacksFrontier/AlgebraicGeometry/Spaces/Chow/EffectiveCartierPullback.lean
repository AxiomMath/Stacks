module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Pulling back a section and its divisor along a morphism of good algebraic spaces

In the situation of Stacks 0EDT let `f : X' → X` be a morphism of good algebraic spaces over
`B` and let `(ℒ, s, i : E → X)` be a triple as in Stacks 0ER1, so `ℒ` is an invertible sheaf on
`X` with a global section `s` and `E = Z(s)` is its vanishing locus.  Stacks 0ER3 sets
`ℒ' = f^*ℒ`, `s' = f^*s` and `E' = X' ×_X E = Z(s')`, and records the resulting commutative
diagram

  `E' → X'`, `E' → E`, `E → X`, `X' → X`,

in which `E' → E` and `E' → X'` are the two projections. The closed subspace written `D` in
Stacks 0ER3 is written `E` here, since `D` denotes the dimension situation.

## Main definitions

* `AlgebraicGeometry.Space.pullbackSheaf` and `AlgebraicGeometry.Space.pullbackGlobalSection`:
  the pulled-back sheaf `ℒ' = f^*ℒ` and section `s' = f^*s`.
* `AlgebraicGeometry.Space.pullbackDivisor`: the closed subspace `E' = X' ×_X E` of `X'`.
* `AlgebraicGeometry.Space.pullbackDivisorProjection`: the morphism `g : E' → E` of the diagram;
  the other leg `i' : E' → X'` is the inclusion of that closed subspace.

## Main results

* `AlgebraicGeometry.Space.pullbackDivisor_isPullback`: the square is cartesian, which is the
  identification `E' = X' ×_X E`.
* `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`: the identification `E' = Z(s')`.
* `AlgebraicGeometry.Space.pullbackDivisor_comm`: the diagram commutes, `g ≫ i = i' ≫ f`.
* `AlgebraicGeometry.Space.pullbackDivisorProjection_comp_structure`: `g` is a morphism over the
  base.
* `AlgebraicGeometry.Space.isInvertibleSheaf_pullbackSheaf`: `ℒ'` is again invertible.

## References

* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

section Pullback

variable (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-! ### The pulled-back sheaf and section -/

/-- The inverse image `ℒ' = f^*ℒ` along `f` of a sheaf of modules `ℒ` on `X`. -/
@[stacks 0ER3 "the sheaf L' = f^*L of the construction, as the inverse image of Stacks 03LU"]
abbrev pullbackSheaf : Modules.{u, u} D.site D.base D.base_mem X' hp'.1 :=
  (modulePullback D.site D.base D.base_mem f).obj L

/-- The inverse image `s' = f^*s` along `f` of a global section `s` of `ℒ`. -/
@[stacks 0ER3 "the section s' = f^*s of the construction, as the inverse image of a global
section along f"]
abbrev pullbackGlobalSection : (pullbackSheaf D p hp p' hp' f L).sections :=
  modulePullbackSections D.site D.base D.base_mem f L s

/-- The inverse image `ℒ' = f^*ℒ` of an invertible sheaf is invertible. -/
theorem isInvertibleSheaf_pullbackSheaf (hL : IsInvertibleSheaf D p hp L) :
    IsInvertibleSheaf D p' hp' (pullbackSheaf D p hp p' hp' f L) :=
  let : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedTopos D.site D.base D.base_mem
        (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos D.site D.base D.base_mem ⟨X, hp.1⟩).O).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  (Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (smallEtaleRingedToposModulesHom D.site D.base D.base_mem f) L).toAlgebraicGeometry _ _ _

/-! ### The pulled-back divisor and its diagram -/

/-- The closed subspace `E' = X' ×_X E` of `X'`: the inverse image along `f` of the vanishing
locus `E = Z(s)`. -/
@[stacks 0ER3 "the closed subspace D' = X' ×_X D of X', taken as the inverse image of D along f
in the sense of Stacks 083Q; its identification with Z(s') is
AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus"]
def pullbackDivisor : ClosedSubspaces D.site D.base D.base_mem X' :=
  ⟨(vanishingLocus D p hp L s).1.preimage f.hom,
    isClosedSubspace_preimage D.site D.base D.base_mem f.hom (vanishingLocus D p hp L s).1
      hp.1 hp'.1 (vanishingLocus D p hp L s).2⟩

/-- The projection `g : E' → E` of the inverse image of the vanishing locus onto that vanishing
locus. -/
def pullbackDivisorProjection :
    (pullbackDivisor D p hp p' hp' f L s).1.toFunctor ⟶ (vanishingLocus D p hp L s).1.toFunctor :=
  (vanishingLocus D p hp L s).1.fromPreimage f.hom

/-- The diagram commutes: `g ≫ i = i' ≫ f`, for `i' : E' → X'` the inclusion of the closed
subspace `E'` and `i : E → X` the inclusion of the vanishing locus. -/
@[stacks 0ER3 "commutativity of the diagram, g ≫ i = i' ≫ f"]
theorem pullbackDivisor_comm :
    pullbackDivisorProjection D p hp p' hp' f L s ≫ (vanishingLocus D p hp L s).1.ι =
      (pullbackDivisor D p hp p' hp' f L s).1.ι ≫ f.hom :=
  Subfunctor.fromPreimage_ι (vanishingLocus D p hp L s).1 f.hom

/-- The square with legs `g : E' → E` and `i' : E' → X'` is cartesian, which is the
identification `E' = X' ×_X E`. -/
@[stacks 0ER3 "the identification D' = X' ×_X D, as the cartesian square with legs g : D' → D
and i' : D' → X'"]
theorem pullbackDivisor_isPullback :
    IsPullback (pullbackDivisorProjection D p hp p' hp' f L s)
      (pullbackDivisor D p hp p' hp' f L s).1.ι (vanishingLocus D p hp L s).1.ι f.hom :=
  Subfunctor.isPullback_preimage f.hom (vanishingLocus D p hp L s).1

/-- The identification `E' = Z(s')`: for an invertible `ℒ`, the inverse image along `f` of the
vanishing locus of `s` is the vanishing locus of the pulled-back section `s' = f^*s`. -/
@[stacks 0ER3 "the identification D' = Z(s'), the vanishing locus of the pulled-back section"]
theorem pullbackDivisor_eq_vanishingLocus (hL : IsInvertibleSheaf D p hp L) :
    pullbackDivisor D p hp p' hp' f L s =
      vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s) :=
  (zeroScheme_modulePullback_eq_preimage D.site D.base D.base_mem f L s hL).symm

/-- The projection `g : E' → E` is a morphism over the base: composing it with the structure
morphism of `E` gives the structure morphism of `E'`. -/
theorem pullbackDivisorProjection_comp_structure (hf : f.hom ≫ p = p') :
    pullbackDivisorProjection D p hp p' hp' f L s ≫ ((vanishingLocus D p hp L s).1.ι ≫ p) =
      (pullbackDivisor D p hp p' hp' f L s).1.ι ≫ p' := by
  rw [← Category.assoc, pullbackDivisor_comm, Category.assoc, hf]

end Pullback

end AlgebraicGeometry.Space

end
