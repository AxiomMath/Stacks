module

public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Extremally disconnected covers of a quasi-compact Hausdorff space

A cover of a quasi-compact Hausdorff space `X` is a continuous surjection `π : X' → X` with `X'`
quasi-compact Hausdorff and extremally disconnected. It is *minimal* when no proper closed subset
of `X'` surjects onto `X`. Such covers exist, and minimal ones are unique up to homeomorphism
over `X`.

## Main results

* `exists_extremallyDisconnected_cover` (Stacks 090D): every quasi-compact Hausdorff space has an
  extremally disconnected cover.
* `minimal_cover_unique` (Stacks 090D): two minimal extremally disconnected covers of the same
  quasi-compact Hausdorff space are homeomorphic over it.
-/

@[expose] public section

open Function Set Topology

universe u

/-! ## Existence -/

/-- `Ultrafilter X` is a projective object in the category of quasi-compact Hausdorff spaces. -/
theorem ultrafilter_projective (X : Type u) :
    CompactT2.Projective (Ultrafilter X) := by
  intro Y Z _ _ _ _ _ _ f g f_cont g_cont g_surj
  -- pick a right inverse for `g`
  let s : Z → Y := fun z => Classical.choose (g_surj z)
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_surj z)
  -- transport `f` to `Y` via `s` and extend to the Stone-Cech-like object
  let t : X → Y := s ∘ f ∘ (pure : X → Ultrafilter X)
  refine ⟨Ultrafilter.extend t, continuous_ultrafilter_extend t, ?_⟩
  -- check `g ∘ Ultrafilter.extend t = f` by density of `pure`
  refine denseRange_pure.equalizer (g_cont.comp (continuous_ultrafilter_extend t)) f_cont ?_
  -- on the dense range `pure`, both sides agree because `Ultrafilter.extend t ∘ pure = t`
  have h1 : Ultrafilter.extend t ∘ (pure : X → Ultrafilter X) = t :=
    ultrafilter_extend_extends t
  rw [Function.comp_assoc, h1]
  simp only [t]
  rw [← Function.comp_assoc, hs, Function.id_comp]

/-- `Ultrafilter X` is extremally disconnected. -/
private theorem ultrafilter_extremallyDisconnected (X : Type u) :
    ExtremallyDisconnected (Ultrafilter X) :=
  CompactT2.Projective.extremallyDisconnected (ultrafilter_projective X)

/-- **Stacks 090D, existence half.** Every compact Hausdorff space `X` admits a
continuous surjection from a compact Hausdorff extremally disconnected space. -/
@[stacks 090D]
theorem exists_extremallyDisconnected_cover
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : CompactSpace X')
        (_ : T2Space X') (_ : ExtremallyDisconnected X')
        (π : X' → X), Continuous π ∧ Function.Surjective π := by
  refine ⟨Ultrafilter X, inferInstance, inferInstance, inferInstance,
    ultrafilter_extremallyDisconnected X, Ultrafilter.extend id,
    continuous_ultrafilter_extend id, ?_⟩
  -- `Ultrafilter.extend id ∘ pure = id`, so the extension is surjective.
  intro x
  exact ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (id : X → X)) x⟩

/-! ## Uniqueness for minimal covers -/

/-- **Stacks 090D, uniqueness half.** If `π' : X' → X` and `π'' : X'' → X` are
two minimal extremally disconnected covers of a compact Hausdorff space `X`,
then there is a homeomorphism `X' ≃ₜ X''` lying over `X`.

Here "minimal" means: no proper closed subset surjects onto `X`. -/
@[stacks 090D]
theorem minimal_cover_unique
    {X X' X'' : Type u}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] [ExtremallyDisconnected X']
    [TopologicalSpace X''] [CompactSpace X''] [T2Space X''] [ExtremallyDisconnected X'']
    {π' : X' → X} (π'_cont : Continuous π') (π'_surj : Function.Surjective π')
    (π'_min : ∀ E : Set X', IsClosed E → E ≠ univ → π' '' E ≠ univ)
    {π'' : X'' → X} (π''_cont : Continuous π'') (π''_surj : Function.Surjective π'')
    (π''_min : ∀ E : Set X'', IsClosed E → E ≠ univ → π'' '' E ≠ univ) :
    ∃ φ : X' ≃ₜ X'', π'' ∘ φ = π' := by
  -- (1) Projectivity of `X'` lifts `π'` through `π''`.
  have hproj : CompactT2.Projective X' :=
    CompactT2.ExtremallyDisconnected.projective
  obtain ⟨g, g_cont, g_eq⟩ := hproj π'_cont π''_cont π''_surj
  -- We have `π'' ∘ g = π'`.
  -- (2) `g` is surjective: its image is closed and surjects onto `X`, so by
  -- minimality of `X''` the image equals `univ`.
  have g_closed : IsClosedMap g := g_cont.isClosedMap
  have range_closed : IsClosed (range g) := by
    simpa [Set.image_univ] using g_closed _ isClosed_univ
  -- `π''` carries `g '' E` onto `π' '' E`, since `π'' ∘ g = π'`.
  have himage : ∀ E : Set X', π'' '' (g '' E) = π' '' E := fun E => by
    rw [← Set.image_comp, g_eq]
  have g_surj : Function.Surjective g := by
    rw [← Set.range_eq_univ]
    by_contra h
    -- `range g` is closed, proper, and surjects onto `X`; contradicts minimality.
    refine π''_min (range g) range_closed h ?_
    rw [← Set.image_univ, himage, Set.image_univ, Set.range_eq_univ.mpr π'_surj]
  -- (3) Zorn condition for `g`: every proper closed subset of `X'` fails to
  -- surject under `g` (else, applying `π''`, we contradict minimality of `X'`).
  have g_zorn : ∀ E : Set X', E ≠ univ → IsClosed E → g '' E ≠ univ := by
    intro E hEne hEcl hEsurj
    refine π'_min E hEcl hEne ?_
    rw [← himage, hEsurj, Set.image_univ, Set.range_eq_univ.mpr π''_surj]
  -- (4) Now invoke Stacks lemma 08YL = `ExtremallyDisconnected.homeoCompactToT2`.
  refine ⟨ExtremallyDisconnected.homeoCompactToT2 g_cont g_surj g_zorn, ?_⟩
  funext x
  -- The underlying function of the homeomorphism is `g`.
  exact congr_fun g_eq x

end
