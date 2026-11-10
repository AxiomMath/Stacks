module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionIsoOffCurve
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The contraction is birational, and its centre is a nonzero ideal

Two of the binders that
`AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isBirational`
still carries are `hI0`, that the vanishing ideal of the image point is nonzero, and `hbir`,
that the morphism is birational. They look unrelated and they are not: **both need the single
fact that the base has a point other than the image point `y`**, and nothing else that is not
already available. This file proves that fact and discharges both.

The fact comes from the dimension hypothesis the chain already carries. If `y` were the only
point of `Y` then `Y` would be discrete, so `topologicalKrullDim Y = 0`
(`topologicalKrullDim_zero_of_discreteTopology`); but the local ring at a point never has larger
dimension than the space (`AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim`), and
`hdim` says that local ring has dimension two. So `Y` has a second point, and:

* `hI0` is then `AlgebraicGeometry.vanishingIdeal_singleton_ne_bot`, which asks exactly for a
  point different from `y` on a reduced scheme;
* `hbir` needs a little more. The generic point of `Y` is not `y`: a closed point equal to the
  generic point would have `{y} = closure {y} = Y`, making `Y` a single point again. So the
  generic point lies in `W = Y ∖ {y}`, over which
  `AlgebraicGeometry.isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt` already makes `f` an
  isomorphism — and a morphism of integral schemes that is an isomorphism over an open
  containing the generic point of the target is birational.

That last step is the content of
`AlgebraicGeometry.isBirational_of_isIso_morphismRestrict_of_genericPoint_mem`, and it is proved
with no reference to blowups: the generic point of `Y` is in the image, so
`f(η_X) ⤳ η_Y` by continuity while `η_Y ⤳ f(η_X)` because `η_Y` is generic, and a scheme is
`T0`, so the two points are equal; the isomorphism of local rings at `η_X` is then transported
from `f|_W` along `AlgebraicGeometry.morphismRestrictStalkMap`.

## Main results

* `AlgebraicGeometry.exists_ne_of_ringKrullDim_stalk_eq_two` — a scheme with a point whose local
  ring has dimension two has a second point.
* `AlgebraicGeometry.vanishingIdeal_singleton_ne_bot_of_ringKrullDim_stalk_eq_two` — **`hI0`
  discharged.**
* `AlgebraicGeometry.genericPoint_ne_of_isClosed_of_ringKrullDim_stalk_eq_two` — such a point,
  if closed, is not the generic point.
* `AlgebraicGeometry.isBirational_of_isIso_morphismRestrict_of_genericPoint_mem` — a morphism of
  integral schemes which is an isomorphism over an open containing the generic point of the
  target is birational.
* `AlgebraicGeometry.isBirational_of_steinSetup` — **`hbir` discharged** for a morphism carrying
  an `AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`, from `hdim` alone.
* `AlgebraicGeometry.isBirational_of_steinSetup` — **`hbir` discharged** for a morphism
  carrying an `AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`, from `hdim`
  alone.

## What became of the integrality

The integrality hypothesis is a surplus one: it shrinks to reducedness once the classifying
morphism is shown birational without it, and this is done in
`StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionReduced.lean`: the
integrality-free birationality criterion
`AlgebraicGeometry.isBirational_of_isIso_morphismRestrict` is public, and produces
`IsBirational g` directly, so `hintegral`, `hI0` and `hbir` all disappear
and `[IsIntegral X]` weakens to `[IsReduced X]`. The 0C2L statement to read is the one there;
what is here are the reusable pieces, including
`AlgebraicGeometry.isBirational_of_steinSetup`, which records that `f` itself is
birational.

Section [Stacks, Tag 0C2I], in which 0C2L lives, carries no standing situation: it opens with a
*definition* of "exceptional curve of the first kind", the word "integral" does not occur
anywhere in it, and each of its lemmas restates "let `X` be a Noetherian scheme" from scratch,
which a lemma under a standing situation would not do. (The *following* section of the source
does open with a standing "integral Noetherian schemes regular of dimension two" — so the
chapter uses that device, just not here.) So `[IsReduced X]`, the one hypothesis of this kind
that remains anywhere in the chain, must still be named by whatever carrier eventually takes the
tag.

## References

* [Stacks Project, Tag 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A scheme with a point whose local ring has Krull dimension two has a second point.** Were
`y` the only point, the space would be discrete and so of topological Krull dimension zero,
while the local ring at a point never exceeds the dimension of the space. -/
public theorem exists_ne_of_ringKrullDim_stalk_eq_two {Y : Scheme.{u}} (y : Y)
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    ∃ y₀ : Y, y₀ ≠ y := by
  by_contra hno
  have heq : ∀ a : Y, a = y := fun a ↦ by_contra fun hne ↦ hno ⟨a, hne⟩
  have hsub : Subsingleton Y := ⟨fun a b ↦ (heq a).trans (heq b).symm⟩
  have h0 : topologicalKrullDim Y ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  have hle := ringKrullDim_stalk_le_topologicalKrullDim (X := Y) y
  rw [hdim] at hle
  exact absurd (hle.trans h0) (by decide)

/-- **The binder `hI0` discharged.** On a reduced scheme the vanishing ideal of a closed point
whose local ring has dimension two is nonzero, because the dimension forces a second point and
`AlgebraicGeometry.vanishingIdeal_singleton_ne_bot` asks for nothing more. -/
public theorem vanishingIdeal_singleton_ne_bot_of_ringKrullDim_stalk_eq_two {Y : Scheme.{u}}
    [IsReduced Y] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ≠ ⊥ :=
  let ⟨_y₀, hy₀⟩ := exists_ne_of_ringKrullDim_stalk_eq_two y hdim
  vanishingIdeal_singleton_ne_bot y hy hy₀

/-- **A closed point whose local ring has dimension two is not the generic point.** Otherwise
`{y}`, being closed, would equal the closure of the generic point, that is the whole space,
leaving `Y` with no second point. -/
public theorem genericPoint_ne_of_isClosed_of_ringKrullDim_stalk_eq_two {Y : Scheme.{u}}
    [IrreducibleSpace Y] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    genericPoint Y ≠ y := by
  intro hgen
  obtain ⟨y₀, hy₀⟩ := exists_ne_of_ringKrullDim_stalk_eq_two y hdim
  have hclos : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_closure Y
  rw [hgen, hy.closure_eq] at hclos
  have hmem : y₀ ∈ ({y} : Set Y) := by rw [hclos]; trivial
  exact hy₀ hmem

/-- **A morphism of integral schemes which is an isomorphism over an open containing the generic
point of the target is birational.**

The generic point `η_Y` lies in the image, say `f x = η_Y`. Then `f(η_X) ⤳ f x = η_Y` because
`η_X ⤳ x` and `f` is continuous, while `η_Y ⤳ f(η_X)` because `η_Y` is generic; a scheme is
`T0`, so `f(η_X) = η_Y`, which is the bijection on generic points. The isomorphism of local
rings at `η_X` then comes from `AlgebraicGeometry.isBirational_of_isIso_morphismRestrict`, which
does the generic-point bookkeeping once and for all; this lemma supplies only its two pointwise
hypotheses, which on integral schemes reduce to the single membership `hηY`.

The name is longer than it needs to be on purpose:
`AlgebraicGeometry.isBirational_of_isIso_morphismRestrict` asks instead for the generic points of
*both* schemes to land in the open, and assumes no integrality; this one trades those two
pointwise binders for the integrality that the chapter grants anyway. -/
@[ega "I 6.5.5" "(ii), special case"]
public theorem isBirational_of_isIso_morphismRestrict_of_genericPoint_mem
    {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (W : Y.Opens) (hiso : IsIso (f ∣_ W))
    (hηY : genericPoint Y ∈ W) :
    IsBirational f := by
  obtain ⟨x', hx'⟩ := (Scheme.homeoOfIso (asIso (f ∣_ W))).surjective ⟨genericPoint Y, hηY⟩
  have hx'eq : f.base x'.1 = genericPoint Y := by
    have hcoe := morphismRestrict_base_coe f W x'
    rw [← hcoe]
    exact congrArg Subtype.val hx'
  have hgen : f.base (genericPoint X) = genericPoint Y := by
    have h1 : genericPoint X ⤳ x'.1 := genericPoint_specializes _
    have h2 : f.base (genericPoint X) ⤳ f.base x'.1 := h1.map f.continuous
    rw [hx'eq] at h2
    exact (h2.antisymm (genericPoint_specializes _)).eq
  have hmem : genericPoint X ∈ f ⁻¹ᵁ W := by
    change f.base (genericPoint X) ∈ W
    rw [hgen]
    exact hηY
  refine isBirational_of_isIso_morphismRestrict f W hiso ?_ ?_
  all_goals
    intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    first | exact hx ▸ hmem | exact hx ▸ hηY

/-- A morphism of integral schemes carrying an
`AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup` is birational as soon as the
local ring at the image point has dimension two.

That dimension puts the generic point of the base inside `W = Y ∖ {y}`
(`AlgebraicGeometry.genericPoint_ne_of_isClosed_of_ringKrullDim_stalk_eq_two`), and over `W` the
morphism is an isomorphism by
`AlgebraicGeometry.isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt`: the setup grants
`f_* 𝒪_X = 𝒪_Y`, and every point over `W` is off the curve because the curve is carried to `y`. -/
public theorem isBirational_of_steinSetup {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {D : X.IdealSheafData} (f : X ⟶ Y) (y : Y) (hsetup : D.IsSteinContractionSetup f y)
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    IsBirational f := by
  have := hsetup.isProper
  have := hsetup.isIso_c
  obtain ⟨W, hWc⟩ : ∃ W : Y.Opens, (W : Set Y) = ({y} : Set Y)ᶜ :=
    ⟨⟨{y}ᶜ, hsetup.isClosed_singleton.isOpen_compl⟩, rfl⟩
  have hsupp : ∀ x ∈ (D.support : Set X), f.base x = y :=
    (D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hsetup.base_eq
  have hiso : IsIso (f ∣_ W) := by
    refine isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt f W fun x hx ↦
      hsetup.quasiFinite_of_notMem x fun hmem ↦ ?_
    have hxW : f.base x ∈ ({y} : Set Y)ᶜ := hWc ▸ hx
    exact hxW (hsupp x hmem)
  refine isBirational_of_isIso_morphismRestrict_of_genericPoint_mem f W hiso ?_
  rw [← SetLike.mem_coe, hWc]
  exact genericPoint_ne_of_isClosed_of_ringKrullDim_stalk_eq_two y hsetup.isClosed_singleton hdim

end AlgebraicGeometry

end
