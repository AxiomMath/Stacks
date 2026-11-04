module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.UpperShriekStructureSheafTrivial
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.Generizations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Gorenstein step of Tag 0EA3 on a Cohen–Macaulay neighbourhood

In the proof of [Stacks, Tag 0EA3] the scheme `X` is first shrunk around `x` so that it is affine
and Cohen–Macaulay: the Cohen–Macaulay locus is open ([Stacks, Tag 0AWT], applied to the
dualizing complex `f^!𝒪_Y` of [Stacks, Tag 0AA3] on an affine neighbourhood), and `𝒪_{X, x}` is
Cohen–Macaulay. On such a neighbourhood every point of dimension at most one lies outside
`closure {x}`, so `f` is étale there, and
`Stacks.PurityRamification.isGorenstein_of_isCohenMacaulay_of_etaleAt` shows that the
neighbourhood, hence `𝒪_{X, x}`, is Gorenstein.

## Main results

* `Stacks.PurityRamification.exists_isAffineOpen_isCohenMacaulay` — an affine Cohen–Macaulay open
  neighbourhood of a Cohen–Macaulay point of a scheme of finite type over a regular local ring.
* `Stacks.PurityRamification.etaleAt_of_ringKrullDim_le_one` — in the situation of Tag 0EA3, `f`
  is étale at every point whose local ring has dimension at most one.
* `Stacks.PurityRamification.isGorensteinLocalRing_stalk_of_isCohenMacaulay` — `𝒪_{X, x}` is
  Gorenstein when `X` is affine and Cohen–Macaulay.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality

universe u

namespace Stacks.PurityRamification

/-- The stalk of an open subscheme at `y` is Cohen–Macaulay iff the stalk of `X` at `y` is. -/
private theorem isCohenMacaulayLocalRing_stalk_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (y : U.toScheme) :
    IsCohenMacaulayLocalRing (U.toScheme.presheaf.stalk y) ↔
      IsCohenMacaulayLocalRing (X.presheaf.stalk y.1) :=
  _root_.isCohenMacaulayLocalRing_iff_of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv

/-- **An affine Cohen–Macaulay neighbourhood.** Let `A` be a regular local ring, `f : X ⟶ Spec A`
locally of finite type and `x ∈ X` a point with Cohen–Macaulay local ring. Then `x` has an affine
open neighbourhood which is a Cohen–Macaulay scheme. On an affine open neighbourhood `U₀` the
complex `(U₀ ⟶ Spec A)^!𝒪` is dualizing ([Stacks, Tag 0AA3]), so the Cohen–Macaulay locus of
`U₀` is open ([Stacks, Tag 0AWT], clause (3)); any affine open of `X` inside its image will do. -/
@[ega "IV 7.3.19" "(ii), special case"]
theorem exists_isAffineOpen_isCohenMacaulay {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (x : X) (hx : IsCohenMacaulayLocalRing (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ AlgebraicGeometry.IsCohenMacaulay U.toScheme := by
  have hbasis : ∀ W : Set X, x ∈ W → IsOpen W →
      ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ (U : Set X) ⊆ W := fun W hxW hW => by
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW hW
    exact ⟨U, hU, hxU, hUW⟩
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := hbasis _ (Set.mem_univ x) isOpen_univ
  have : IsAffine U₀.toScheme := hU₀
  let h₀ : U₀.toScheme ⟶ Spec (.of A) := U₀.ι ≫ f
  obtain ⟨j, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine h₀
  have hK := isDualizingComplex_upperShriek_obj (ftsHomToBase h₀) j _
    (isDualizingComplex_derivedStructureSheaf_spec A)
  have hopen := isOpen_setOf_isCohenMacaulayLocalRing (X := U₀.toScheme) _ hK
  let C₀ : Set U₀.toScheme := {y | IsCohenMacaulayLocalRing (U₀.toScheme.presheaf.stalk y)}
  obtain ⟨U, hU, hxU, hUsub⟩ := hbasis (U₀.ι '' C₀)
    ⟨⟨x, hxU₀⟩, (isCohenMacaulayLocalRing_stalk_iff U₀ ⟨x, hxU₀⟩).mpr hx, rfl⟩
    (U₀.ι.isOpenEmbedding.isOpenMap _ hopen)
  refine ⟨U, hU, hxU, ?_⟩
  have h := (AlgebraicGeometry.isCohenMacaulay_tfae_stalk U.toScheme).out 1 2
  refine h.mpr ⟨inferInstance, fun y => ⟨inferInstance, ?_⟩⟩
  obtain ⟨y₀, hy₀, hy₀y⟩ := hUsub y.2
  have hy : IsCohenMacaulayLocalRing (X.presheaf.stalk y.1) := by
    have := (isCohenMacaulayLocalRing_stalk_iff U₀ y₀).mp hy₀
    rwa [show y₀.1 = y.1 from hy₀y] at this
  exact (isCohenMacaulayLocalRing_stalk_iff U y).mpr hy

/-- **`f` is étale at the points of dimension at most one.** If `𝒪_{X, x}` has dimension at least
two and `f` is étale outside `closure {x}`, then `f` is étale at every point whose local ring has
dimension at most one: such a point is not a specialization of `x`, the dimension of the local
ring being monotone along specialization. -/
theorem etaleAt_of_ringKrullDim_le_one {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) (z : X)
    (hz : ringKrullDim (X.presheaf.stalk z) ≤ 1) : EtaleAt f z := by
  refine het z fun hzx => ?_
  have hle := AlgebraicGeometry.ringKrullDim_stalk_le_of_specializes
    (specializes_iff_mem_closure.mpr hzx)
  exact absurd (hx.trans (hle.trans hz)) (by decide)

/-- **`𝒪_{X, x}` is Gorenstein** (the first part of the proof of [Stacks, Tag 0EA3]). Let `A` be
a regular local ring, `f : X ⟶ Spec A` locally of finite type with `X` affine and
Cohen–Macaulay, and `x ∈ X` a point whose local ring has dimension at least two, such that `f`
is étale outside `closure {x}`. Then `X` is Gorenstein
(`Stacks.PurityRamification.isGorenstein_of_isCohenMacaulay_of_etaleAt`), in particular
`𝒪_{X, x}` is a Gorenstein local ring. -/
theorem isGorensteinLocalRing_stalk_of_isCohenMacaulay {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsAffine X]
    [LocallyOfFiniteType f] (hCM : AlgebraicGeometry.IsCohenMacaulay X) (x : X)
    (hx : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isGorenstein_of_isCohenMacaulay_of_etaleAt f hCM
    (etaleAt_of_ringKrullDim_le_one f x hx het)
  exact AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing x

end Stacks.PurityRamification

end
