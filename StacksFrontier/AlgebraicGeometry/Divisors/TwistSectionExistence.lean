module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroSections.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.MinimalTwistSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection

/-!
# A global section of `𝒪_X(D)` that is not a section of `𝒪_X`

Let `D` be an effective Cartier divisor on a scheme `X` over a field `k`, with inclusion `i`. If
`H¹(X, 𝒪_X)` is finite-dimensional of dimension `< d` and `H⁰(X, i_* i^* 𝒪_X(D))` has dimension
`≥ d`, the long exact cohomology sequence of `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* i^* 𝒪_X(D) ⟶ 0` gives a
global section of `𝒪_X(D)` which is not a section of `𝒪_X`. This is the cohomological step of
the proof of [Stacks, Tag 0A27].

## Main results

* `Stacks.SheafOfModules.exists_notMem_range_sectionsMap_of_forall_app_ne`: an element of
  `N(⊤)` outside the image of `M(⊤)` is a global section of `N` outside the image of the global
  sections of `M`.
* `Stacks.Divisors.exists_notMem_range_unitToInvertibleSheaf`: there is a global section of
  `𝒪_X(D)` which is not a section of `𝒪_X`, as soon as `H¹(X, 𝒪_X)` is finite-dimensional of
  dimension `< d` and `H⁰(X, i_* i^* 𝒪_X(D))` has dimension `≥ d`.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_minimal_of_finrank`: the inner claim of
  [Stacks, Tag 0A27], that `X ∖ {x}` is affine, from a minimal twist and the two dimension
  bounds.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveSpaceSections

universe u

namespace Stacks.SheafOfModules

/-- **A section over `⊤` outside the image of `M(⊤)` is a global section outside the image of
the global sections of `M`.** -/
theorem exists_notMem_range_sectionsMap_of_forall_app_ne {T : TopCat.{u}}
    {R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (f : M ⟶ N)
    {σ : N.val.obj (op ⊤)} (h : ∀ t : M.val.obj (op ⊤), f.val.app (op ⊤) t ≠ σ) :
    ∃ s : N.sections, s ∉ Set.range (_root_.SheafOfModules.sectionsMap f) := by
  refine ⟨sectionsOfTopOfRingSheaf N σ, ?_⟩
  rintro ⟨u, hu⟩
  refine h (u.eval (op ⊤)) ?_
  show (_root_.SheafOfModules.sectionsMap f u).eval (op ⊤) = σ
  rw [hu, sectionsOfTopOfRingSheaf_eval_top]

end Stacks.SheafOfModules

namespace Stacks.Divisors

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- **A global section of `𝒪_X(D)` that is not a section of `𝒪_X`.** For an effective Cartier
divisor `D ⊆ X` with inclusion `i`, if `H¹(X, 𝒪_X)` is finite-dimensional of dimension `< d`
and `H⁰(X, i_* i^* 𝒪_X(D))` has dimension `≥ d`, then some global section of `𝒪_X(D)` is not
the image of any global section of `𝒪_X`. -/
theorem exists_notMem_range_unitToInvertibleSheaf (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D]
    [FiniteDimensional k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1)]
    {d : ℕ}
    (hd : Module.finrank k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1) < d)
    (hd' : d ≤ Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (modulesInvertibleSheaf D))) 0)) :
    ∃ s : (invertibleSheaf D).sections,
      s ∉ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf D)) := by
  obtain ⟨_, hSE⟩ := isShortExactUnitSequence_canonicalSections D
  obtain ⟨σ, hσ⟩ := AlgebraicGeometry.exists_forall_app_ne_of_le_finrank k f hSE hd hd'
  exact Stacks.SheafOfModules.exists_notMem_range_sectionsMap_of_forall_app_ne
    (unitToInvertibleSheaf D) hσ

/-- **The inner claim of [Stacks, Tag 0A27] from a minimal twist and the dimension count.** Let
`X` be a proper curve over `k`, locally Noetherian and integral, and let `x` be a closed point at
which `𝒪_{X,x}` is a discrete valuation ring. Given

* `g`, `hg`: a morphism `ℐ_{(p+1)x} ⟶ ℐ_{p·x}` of ideal sheaves over the two inclusions into
  `𝒪_X`;
* `hlocal`: a germ of `𝒪_X((p+1)x)` at `x` that does not generate the stalk comes from
  `𝒪_X(p·x)`;
* `hmin`: every global section of `𝒪_X(p·x)` is a section of `𝒪_X`;
* `hd`, `hd'`: `dim_k H¹(X, 𝒪_X) < d ≤ dim_k H⁰(X, i_* i^* 𝒪_X((p+1)x))`;

then `X ∖ {x}` is affine. -/
theorem isAffineOpen_compl_singleton_of_minimal_of_finrank
    [IsLocallyNoetherian X] [IsIntegral X]
    (hf : IsProper f) (hc : IsCurve k f) {x : X} (hx : IsClosed ({x} : Set X))
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {p : ℕ}
    (g : negativeTwist
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)) ⟶
      negativeTwist (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p))
    (hg : g ≫ idealInclusion
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p)
      = idealInclusion
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)))
    (hlocal : ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))).sections,
      x ∉ nonvanishingChart (invertibleSheaf
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))) t →
        t ∈ Set.range (_root_.SheafOfModules.sectionsMap (invertibleSheafMap g)))
    (hmin : ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p)).sections,
      t ∈ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p))))
    [FiniteDimensional k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1)]
    {d : ℕ}
    (hd : Module.finrank k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1) < d)
    (hd' : d ≤ Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)).subschemeι).obj
        ((Scheme.Modules.pullback
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)).subschemeι).obj
          (modulesInvertibleSheaf
            (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))))) 0)) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
  have ⟨s, hs⟩ := exists_notMem_range_unitToInvertibleSheaf f
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)) hd hd'
  isAffineOpen_compl_singleton_of_minimal hf hc hx g hg hlocal hmin s hs

end Stacks.Divisors

end
