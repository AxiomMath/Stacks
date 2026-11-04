module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian

/-!
# Exactness of coherent adic systems is local on the base

Let `X` be a Noetherian scheme and `ℐ` a quasi-coherent ideal sheaf on `X`. The category
`Coh(X, ℐ)` of coherent adic systems along `ℐ` is abelian, so a pair of composable morphisms
`F ⟶ G ⟶ H` whose composite vanishes has a homology object, and the pair is exact exactly when
that object is zero. This file proves part (3) of Tag 087X: exactness in `Coh(X, ℐ)` may be
tested on the members of an open covering of `X`.

One implication is formal. Restriction along an open immersion is exact, hence preserves
homology, so it carries an exact short complex to an exact short complex.

The other implication is the substance of the statement. Exactness of a short complex `S` is the
vanishing of the object `H` of any left homology data of `S`, equivalently the vanishing of the
identity morphism of `H`. Here `H` is itself a coherent adic system, and because restriction
preserves homology the restriction of `H` to a member `U j` of the covering is a left homology
object of the restricted short complex; local exactness makes it zero, so the restriction of
`𝟙 H` vanishes. Vanishing of a morphism of coherent adic systems is a local condition, being
levelwise the vanishing of a morphism of sheaves of modules, so `𝟙 H = 0` and `S` is exact.

The hypothesis that the composite of the two morphisms vanishes is itself local for the same
reason, so the criterion needs nothing assumed globally: a pair of morphisms of coherent adic
systems forms an exact sequence precisely when each of its restrictions does.

## Main results

* `Stacks.Coherent.restrictFunctor_map_comp_eq_zero` — restriction along an open immersion
  carries a vanishing composite to a vanishing composite.
* `Stacks.Coherent.comp_eq_zero_of_restrictFunctor_map_comp_eq_zero` — conversely, vanishing of
  a composite of morphisms of coherent adic systems is local on an open covering.
* `Stacks.Coherent.exact_iff_restrict_of_comp_zero` — for a pair of morphisms with vanishing
  composite, exactness may be checked after restricting to the members of an open covering.
* `Stacks.Coherent.exact_iff_restrict` — **part (3) of Tag 087X: a pair of morphisms of coherent
  adic systems is an exact sequence if and only if each of its restrictions to the members of an
  open covering is an exact sequence.**

## Implementation notes

The index type of the covering is kept in a universe of its own, since the criterion is applied
to coverings by affine opens, whose index type lives one universe above the scheme.

The short complex built from the restricted morphisms and the image of the short complex built
from the original morphisms under the restriction functor differ only in their proofs that the
composite vanishes, hence are definitionally equal; the arguments below use this instead of
transporting exactness along an isomorphism of short complexes.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u v

namespace Stacks.Coherent

/-! ### Vanishing of a composite -/

/-- **Restriction along an open immersion carries a vanishing composite of morphisms of coherent
adic systems to a vanishing composite.** Restriction is a functor preserving zero morphisms, so
this is immediate. -/
public theorem restrictFunctor_map_comp_eq_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {F G H : CoherentAdicSystems I} (α : F ⟶ G) (β : G ⟶ H) (hαβ : α ≫ β = 0) :
    (restrictFunctor I f).map α ≫ (restrictFunctor I f).map β = 0 := by
  rw [← Functor.map_comp, hαβ, Functor.map_zero]

/-- **Vanishing of a composite of morphisms of coherent adic systems is a local condition.** If
the composite of the restrictions of `α` and `β` to every member of an open covering of `X`
vanishes, then `α ≫ β = 0`.

Restriction is a functor, so the composite of the restrictions is the restriction of the
composite, and a morphism of coherent adic systems vanishing on an open covering vanishes. -/
public theorem comp_eq_zero_of_restrictFunctor_map_comp_eq_zero {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {F G H : CoherentAdicSystems I}
    (α : F ⟶ G) (β : G ⟶ H) {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ j : J, (restrictFunctor I (U j).ι).map α ≫ (restrictFunctor I (U j).ι).map β = 0) :
    α ≫ β = 0 :=
  hom_eq_zero_of_restrictFunctor_map_eq_zero_system I (α ≫ β) U hU fun j =>
    ((restrictFunctor I (U j).ι).map_comp α β).trans (h j)

/-! ### Exactness is local -/

/-- **Exactness of a short complex of coherent adic systems may be checked on an open covering.**
Given morphisms `α : F ⟶ G` and `β : G ⟶ H` of coherent adic systems with `α ≫ β = 0`, the short
complex they form is exact if and only if its restriction to each member of an open covering of
`X` is exact.

Restriction along an open immersion is exact, hence preserves homology, which gives the forward
implication. For the converse, exactness is the vanishing of the identity morphism of the left
homology object `H` of the short complex; restriction preserves homology, so the restriction of
`H` to a member of the covering is the left homology object of the restricted short complex and
is zero by local exactness, whence the restriction of `𝟙 H` vanishes. Vanishing of a morphism of
coherent adic systems is local, so `𝟙 H = 0`. -/
public theorem exact_iff_restrict_of_comp_zero {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G H : CoherentAdicSystems I} (α : F ⟶ G) (β : G ⟶ H)
    (hαβ : α ≫ β = 0) {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤) :
    (ShortComplex.mk α β hαβ).Exact ↔
      ∀ j : J, ∃ h : (restrictFunctor I (U j).ι).map α ≫ (restrictFunctor I (U j).ι).map β = 0,
        (ShortComplex.mk ((restrictFunctor I (U j).ι).map α)
          ((restrictFunctor I (U j).ι).map β) h).Exact := by
  have hN (j : J) : IsNoetherian (U j).toScheme := isNoetherian_of_isOpenImmersion (U j).ι
  constructor
  · intro hS j
    exact ⟨restrictFunctor_map_comp_eq_zero I (U j).ι α β hαβ,
      hS.map (restrictFunctor I (U j).ι)⟩
  · intro hloc
    refine (ShortComplex.mk α β hαβ).leftHomologyData.exact_iff.mpr
      ((IsZero.iff_id_eq_zero _).mpr ?_)
    refine hom_eq_zero_of_restrictFunctor_map_eq_zero_system I
      (𝟙 (ShortComplex.mk α β hαβ).leftHomologyData.H) U hU fun j => ?_
    exact ((restrictFunctor I (U j).ι).map_id _).trans
      ((((ShortComplex.mk α β hαβ).leftHomologyData.exact_map_iff
        (restrictFunctor I (U j).ι)).mp (hloc j).2).eq_of_src _ _)

/-- **Part (3) of Tag 087X: exactness in `Coh(X, ℐ)` may be checked on an open covering of `X`.**
A pair of morphisms `α : F ⟶ G` and `β : G ⟶ H` of coherent adic systems on a Noetherian scheme
is an exact sequence if and only if, for every member `U j` of an open covering of `X`, the
restrictions of `α` and `β` to `U j` form an exact sequence.

Both the condition that the composite vanish and the exactness of the resulting short complex are
local. -/
@[stacks 087X "exactness may be checked on an open covering"]
public theorem exact_iff_restrict {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    {F G H : CoherentAdicSystems I} (α : F ⟶ G) (β : G ⟶ H)
    {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤) :
    (∃ h : α ≫ β = 0, (ShortComplex.mk α β h).Exact) ↔
      ∀ j : J, ∃ h : (restrictFunctor I (U j).ι).map α ≫ (restrictFunctor I (U j).ι).map β = 0,
        (ShortComplex.mk ((restrictFunctor I (U j).ι).map α)
          ((restrictFunctor I (U j).ι).map β) h).Exact := by
  refine ⟨fun ⟨hαβ, hS⟩ => (exact_iff_restrict_of_comp_zero I α β hαβ U hU).mp hS,
    fun hloc => ?_⟩
  have hαβ : α ≫ β = 0 :=
    comp_eq_zero_of_restrictFunctor_map_comp_eq_zero I α β U hU fun j => (hloc j).1
  exact ⟨hαβ, (exact_iff_restrict_of_comp_zero I α β hαβ U hU).mpr hloc⟩

end Stacks.Coherent

end
