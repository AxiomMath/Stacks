module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionReduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The thickening tower of the curve against the infinitesimal tower of the base

Step 3 of the proof of [Stacks, Tag 0C2L] compares two towers of closed subschemes of `X`: the
thickenings `Eₙ = nE` of the exceptional curve, and the scheme-theoretic preimages
`X ×_Y Spec (𝒪_{Y, y}/𝔪_y ⁿ)` of the infinitesimal neighbourhoods of `y`.  The source establishes
two inclusions,

`Eₙ ⊆ X ×_Y Spec (𝒪_{Y, y}/𝔪_y ⁿ)`  and  `X ×_Y Spec (𝒪_{Y, y}/𝔪_y ᵐ) ⊆ E_{n m}`,

and concludes that the two towers are cofinal, so that the inverse limit of [Stacks, Tag 02OD]
may be computed on the thickenings instead and identified by [Stacks, Tag 0C2K].

This file performs that comparison at the level of ideal sheaves, where the preimage tower is
`(ℐ_y ᵐ) · 𝒪_X` for `ℐ_y` the ideal sheaf of the reduced point `y`.  The first inclusion is
proved outright; the second is reduced to a single topological statement.

## Main results

* `AlgebraicGeometry.comap_vanishingIdeal_singleton_le_of_isReduced_subscheme` — the first
  inclusion in degree one: `ℐ_y · 𝒪_X ≤ D`, for any ideal sheaf `D` whose closed subscheme is
  reduced and all of whose points are carried to `y`.  Reducedness is what makes the
  set-theoretic hypothesis give a scheme-theoretic conclusion, and the exceptional curve of
  [Stacks, Tag 0C2L] has it, its subscheme being a projective line over a field.
* `AlgebraicGeometry.comap_pow_vanishingIdeal_singleton_le_pow` — the first inclusion in every
  degree, `(ℐ_y ᵐ) · 𝒪_X ≤ D ᵐ`, which is `Eₘ ⊆ X ×_Y Spec (𝒪_{Y, y}/𝔪_y ᵐ)`.
* `AlgebraicGeometry.exists_pow_le_comap_vanishingIdeal_singleton` — the second inclusion,
  `∃ n, D ⁿ ≤ ℐ_y · 𝒪_X`, from the one topological hypothesis that the set-theoretic fibre over
  `y` is contained in the support of `D`.
* `AlgebraicGeometry.exists_forall_pow_le_comap_pow_vanishingIdeal_singleton` — the two
  inclusions together: the cofinality of the two towers, in the ideal-sheaf spelling.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The closed subscheme of an exceptional curve of the first kind is reduced**, being
isomorphic to a projective line over a field. -/
public theorem isReduced_subscheme_of_projectiveLineProj_iso {X : Scheme.{u}}
    {D : X.IdealSheafData} (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme) :
    IsReduced D.subscheme :=
  isReduced_of_isOpenImmersion (Y := projectiveLineProj k) e.inv

/-- A point lies in the support of the ideal sheaf of the closed point `y` iff it equals `y`. -/
private theorem mem_support_vanishingIdeal_singleton_iff {Y : Scheme.{u}} {y : Y}
    (hy : IsClosed ({y} : Set Y)) (z : Y) :
    z ∈ (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support ↔ z = y := by
  rw [← Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    supportSet_vanishingIdeal_singleton hy]
  rfl

/-- **The scheme-theoretic fibre over `y` contains every reduced closed subscheme carried to
`y`.** In ideal-sheaf terms `ℐ_y · 𝒪_X ≤ D`, for `ℐ_y` the ideal sheaf of the reduced point `y`.

This is the first inclusion of step 3 of [Stacks, Tag 0C2L] in degree one, `E ⊆ X_y`.  A reduced
closed subscheme is the reduced induced structure on its support
(`AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme`), and for
such a subscheme the containment is equivalent to the set-theoretic one
(`AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal`), which `hmaps`
gives. -/
@[ega "I 5.2.4" "special case"]
public theorem comap_vanishingIdeal_singleton_le_of_isReduced_subscheme {X Y : Scheme.{u}}
    (D : X.IdealSheafData) [IsReduced D.subscheme] (f : X ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f ≤ D := by
  have hsupp : ∀ x ∈ (D.support : Set X), f.base x = y :=
    (D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hmaps
  have hD : D = Scheme.IdealSheafData.vanishingIdeal D.support :=
    D.eq_vanishingIdeal_of_isReduced_subscheme D.support rfl
  rw [hD, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.support_comap]
  intro x hx
  exact (mem_support_vanishingIdeal_singleton_iff hy _).2 (hsupp x hx)

/-- **`Eₘ ⊆ X ×_Y Spec (𝒪_{Y, y}/𝔪_y ᵐ)`**, the first inclusion of step 3 of
[Stacks, Tag 0C2L] in every degree.  The inverse-image ideal sheaf is multiplicative
(`Stacks.IdealSheaf.comap_pow`), so the degree-one inclusion raises to the `m`-th power. -/
public theorem comap_pow_vanishingIdeal_singleton_le_pow {X Y : Scheme.{u}}
    (D : X.IdealSheafData) [IsReduced D.subscheme] (f : X ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y) (m : ℕ) :
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) ^ m).comap f ≤ D ^ m := by
  rw [Stacks.IdealSheaf.comap_pow]
  exact pow_le_pow_left'
    (comap_vanishingIdeal_singleton_le_of_isReduced_subscheme D f y hy hmaps) m

/-- **`X_y ⊆ Eₙ` for some `n`**, the second inclusion of step 3 of [Stacks, Tag 0C2L].

The ideal-sheaf consequence of [Stacks, Tag 01Y9] —
`AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le_iff_le_radical`, that a power of one ideal
sheaf lies below another exactly when the first lies below the second's radical — turns this into
the purely topological `hfib`, that the set-theoretic fibre over `y` is contained in the support
of `D`.  In the source `hfib` comes from the fibres of `f` being geometrically connected. -/
public theorem exists_pow_le_comap_vanishingIdeal_singleton {X Y : Scheme.{u}} [IsNoetherian X]
    (D : X.IdealSheafData) (f : X ⟶ Y) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hfib : f.base ⁻¹' ({y} : Set Y) ⊆ (D.support : Set X)) :
    ∃ n : ℕ, D ^ n ≤
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f := by
  rw [Scheme.IdealSheafData.exists_pow_le_iff_le_radical,
    ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.support_comap]
  intro x hx
  exact hfib ((mem_support_vanishingIdeal_singleton_iff hy _).1 hx)

/-- **The two towers are cofinal**, in the ideal-sheaf spelling of step 3 of
[Stacks, Tag 0C2L]: there is an `n` with

`D ^ (n * m) ≤ (ℐ_y ^ m) · 𝒪_X ≤ D ^ m`  for every `m`,

that is, `E_{n m} ⊇ X ×_Y Spec (𝒪_{Y, y}/𝔪_y ᵐ) ⊇ Eₘ`.  The right-hand inclusion is
`AlgebraicGeometry.comap_pow_vanishingIdeal_singleton_le_pow` and the left-hand one is
`AlgebraicGeometry.exists_pow_le_comap_vanishingIdeal_singleton` raised to the `m`-th power. -/
public theorem exists_forall_pow_le_comap_pow_vanishingIdeal_singleton {X Y : Scheme.{u}}
    [IsNoetherian X] (D : X.IdealSheafData) [IsReduced D.subscheme] (f : X ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hfib : f.base ⁻¹' ({y} : Set Y) ⊆ (D.support : Set X)) :
    ∃ n : ℕ, ∀ m : ℕ,
      D ^ (n * m) ≤
          ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) ^ m).comap f ∧
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) ^ m).comap f ≤ D ^ m := by
  obtain ⟨n, hn⟩ := exists_pow_le_comap_vanishingIdeal_singleton D f y hy hfib
  refine ⟨n, fun m => ⟨?_, comap_pow_vanishingIdeal_singleton_le_pow D f y hy hmaps m⟩⟩
  rw [pow_mul, Stacks.IdealSheaf.comap_pow]
  exact pow_le_pow_left' hn m

end AlgebraicGeometry

end
