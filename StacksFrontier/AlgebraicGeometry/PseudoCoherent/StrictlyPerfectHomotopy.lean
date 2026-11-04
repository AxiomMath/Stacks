module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLift

/-!
# Building a null homotopy degree by degree

Let `α : E ⟶ F` be a morphism of cochain complexes indexed by `ℤ` in a preadditive category,
and suppose `E` is concentrated in degrees `[a, b]`. This file constructs a null homotopy of
`α` out of the degreewise lifting problems that the source proof of Stacks 08C7 solves: for
each degree `p` in `[a, b]`, every map `E.X p ⟶ F.X p` killed by the differential of `F` must
factor through `F.d (p - 1) p`.

The induction runs *downwards* from `b`. Having a partial homotopy in degrees above `p`, the
map that remains to be factored in degree `p` is `γ = α.f p - E.d p (p + 1) ≫ h (p + 1)`, and
`γ ≫ F.d p (p + 1) = 0` follows from the homotopy identity one degree up together with
`d ≫ d = 0`. So `γ` is a lifting problem of the stated kind, and its solution is the next
value of the homotopy.

## Main definitions

* `CochainComplex.IsNullHomotopyAt` is the homotopy identity in a single degree for a family
  of maps `E.X p ⟶ F.X q` indexed by the pairs with `q + 1 = p`.

## Main results

* `CochainComplex.nonempty_homotopy_zero_of_exists_lift`: the null homotopy built from the
  degreewise lifting problems.
* `AlgebraicGeometry.RingedSpace.epi_toCycles_of_isZero_homology`: vanishing of the `i`-th
  cohomology sheaf of a complex of `𝒪_X`-modules makes `ℱ^{i-1} ⟶ Z^i(ℱ)` an epimorphism.
* `AlgebraicGeometry.RingedSpace.exists_local_factorization_of_isZero_homology`: on a ringed
  space, one of those degreewise lifting problems is solvable on an open neighbourhood of any
  point, by Stacks 08C6.

## Implementation notes

The family carrying the homotopy is taken to be
`∀ p q : ℤ, q + 1 = p → (E.X p ⟶ F.X q)` rather than `∀ p : ℤ, E.X p ⟶ F.X (p - 1)`. The
second index is redundant, but keeping it — and keeping `CochainComplex.IsNullHomotopyAt`
universally quantified over it — means the identity can be used at `p + 1` without rewriting
`p + 1 - 1` to `p`, so no `eqToHom` or transport appears anywhere. Extending the family by
one degree is `Function.update`, which is already dependent.

The resulting homotopy is produced through
`CochainComplex.HomComplex.Cochain.equivHomotopy`, which identifies a homotopy from `α` to
`0` with a `(-1)`-cochain `z` satisfying `Cochain.ofHom α = δ (-1) 0 z`; the value of
`δ (-1) 0 z` in degree `p` is exactly the right-hand side of
`CochainComplex.IsNullHomotopyAt`.

## References

* [The Stacks Project, Lemma 20.46.5 (08C7)](https://stacks.math.columbia.edu/tag/08C7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TopologicalSpace

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {E F : CochainComplex C ℤ}

/-- The homotopy identity in degree `p` between `α : E ⟶ F` and the zero map, for a family
`h` of maps `E.X p ⟶ F.X q` indexed by the pairs of integers with `q + 1 = p`:
`α.f p = h p (p - 1) ≫ F.d (p - 1) p + E.d p (p + 1) ≫ h (p + 1) p`.

The two neighbouring degrees are taken as universally quantified arguments rather than
written as `p - 1` and `p + 1`, so that the identity can be instantiated at a shifted degree
without rewriting the index arithmetic. -/
def IsNullHomotopyAt (α : E ⟶ F) (h : ∀ p q : ℤ, q + 1 = p → (E.X p ⟶ F.X q)) (p : ℤ) : Prop :=
  ∀ (q r : ℤ) (hq : q + 1 = p) (hr : p + 1 = r),
    α.f p = h p q hq ≫ F.d q p + E.d p r ≫ h r p hr

/-- A morphism out of a complex with a zero term in degree `p` satisfies the homotopy
identity in that degree for any family `h`: both sides are morphisms out of a zero object. -/
theorem isNullHomotopyAt_of_isZero (α : E ⟶ F) (h : ∀ p q : ℤ, q + 1 = p → (E.X p ⟶ F.X q))
    {p : ℤ} (hp : IsZero (E.X p)) : IsNullHomotopyAt α h p :=
  fun _ _ _ _ => hp.eq_of_src _ _

/-- A morphism `α : E ⟶ F` of cochain complexes is null homotopic as soon as `E` is
concentrated in degrees `[a, b]` and, in every degree `p ≥ a`, each map `E.X p ⟶ F.X p`
killed by the differential of `F` factors through `F.d q p` (where `q + 1 = p`).

This is the inductive core of Stacks 08C7: the hypothesis `hlift` is what vanishing of the
cohomology of `F` in degrees `≥ a` provides, locally on a ringed space, when `E.X p` is a
direct summand of a finite free module. -/
theorem nonempty_homotopy_zero_of_exists_lift (α : E ⟶ F) (a b : ℤ)
    (hEa : ∀ p : ℤ, p < a → IsZero (E.X p)) (hEb : ∀ p : ℤ, b < p → IsZero (E.X p))
    (hlift : ∀ p q : ℤ, q + 1 = p → a ≤ p → ∀ γ : E.X p ⟶ F.X p,
      γ ≫ F.d p (p + 1) = 0 → ∃ h : E.X p ⟶ F.X q, h ≫ F.d q p = γ) :
    Nonempty (Homotopy α 0) := by
  classical
  -- Extend a partial homotopy, defined in the degrees above `b - n`, one degree downwards.
  -- The identity holds for free in the degrees below `a`, where `E` vanishes.
  have key : ∀ n : ℕ, ∃ h : ∀ p q : ℤ, q + 1 = p → (E.X p ⟶ F.X q),
      ∀ p : ℤ, b - n < p ∨ p < a → IsNullHomotopyAt α h p := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun _ _ _ => 0, fun p hp => isNullHomotopyAt_of_isZero α _
        (hp.elim (fun hp => hEb p (by omega)) (hEa p))⟩
    | succ n ih =>
      obtain ⟨h, hh⟩ := ih
      by_cases hp₀ : a ≤ b - (n : ℤ)
      · -- The map that remains to be factored in degree `b - n` is killed by `F.d`, because
        -- the homotopy identity holds one degree up and `d ≫ d = 0`.
        have hstep : h (b - n + 1) (b - n) rfl ≫ F.d (b - n) (b - n + 1) =
            α.f (b - n + 1) -
              E.d (b - n + 1) (b - n + 2) ≫ h (b - n + 2) (b - n + 1) (by omega) :=
          eq_sub_of_add_eq
            (hh (b - n + 1) (by omega) (b - n) (b - n + 2) rfl (by omega)).symm
        have hγ : (α.f (b - n) - E.d (b - n) (b - n + 1) ≫ h (b - n + 1) (b - n) rfl) ≫
            F.d (b - n) (b - n + 1) = 0 := by
          rw [sub_comp, Category.assoc, hstep, α.comm, comp_sub, sub_sub_cancel,
            ← Category.assoc, E.d_comp_d, Limits.zero_comp]
        refine ⟨Function.update h (b - n)
          (fun q hq => (hlift (b - n) q hq hp₀ _ hγ).choose), fun p hp q r hq hr => ?_⟩
        by_cases hpa : p < a
        · exact isNullHomotopyAt_of_isZero α _ (hEa p hpa) q r hq hr
        rcases eq_or_lt_of_le (show b - (n : ℤ) ≤ p by omega) with rfl | hlt
        · obtain rfl : r = b - (n : ℤ) + 1 := by omega
          rw [Function.update_self, Function.update_of_ne (by omega),
            (hlift (b - n) q hq hp₀ _ hγ).choose_spec, sub_add_cancel]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hh p (Or.inl hlt) q r hq hr
      · -- Below `a` the terms of `E` vanish, so nothing has to be extended.
        exact ⟨h, fun p hp => hh p (by omega)⟩
  -- Past the lower end of the range of `E` the identity holds in every degree.
  obtain ⟨h, hh⟩ := key (b - a + 1).toNat
  have hall : ∀ p : ℤ, IsNullHomotopyAt α h p := fun p => hh p (by omega)
  refine ⟨(HomComplex.Cochain.equivHomotopy α 0).symm
    ⟨HomComplex.Cochain.mk fun p q hpq => h p q (by omega), ?_⟩⟩
  rw [HomComplex.Cochain.ofHom_zero, add_zero]
  ext p
  rw [HomComplex.Cochain.ofHom_v,
    HomComplex.δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [HomComplex.Cochain.mk_v, Int.negOnePow_zero, one_smul]
  exact hall p (p - 1) (p + 1) (by omega) rfl

end CochainComplex

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- If the `i`-th cohomology sheaf of a complex `ℱ` of `𝒪_X`-modules vanishes then
`ℱ^{i-1} ⟶ Z^i(ℱ)` is an epimorphism: the cohomology sheaf is its cokernel. -/
theorem epi_toCycles_of_isZero_homology {F : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    {i j : ℤ} (hij : j + 1 = i) (hF : IsZero (F.homology i)) : Epi (F.toCycles j i) :=
  epi_of_isZero_cokernel' _
    (F.homologyIsCokernel (i := j) (j := i) (by simp only [CochainComplex.prev]; omega)) hF

/-- The lifting problem that Stacks 08C7 solves in a single degree, solved locally. Let `ℱ`
be a complex of `𝒪_X`-modules with vanishing `i`-th cohomology sheaf, let `𝒜` be a direct
summand of a finite free `𝒪_X`-module and let `γ : 𝒜 ⟶ ℱ^i` be killed by the differential of
`ℱ`. Then every point of `X` has an open neighbourhood over which `γ` factors through
`ℱ^{i-1} ⟶ ℱ^i`.

Indeed `γ` factors through the cycles `Z^i(ℱ)` because it is killed by the differential, and
`ℱ^{i-1} ⟶ Z^i(ℱ)` is an epimorphism by the vanishing of the cohomology sheaf, so Stacks
08C6 applies. -/
theorem exists_local_factorization_of_isZero_homology
    {F : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} {A : StrictlyPerfect.OXMod.{u, u} X}
    (hA : StrictlyPerfect.IsDirectSummandOfFiniteFree A) {i j : ℤ} (hij : j + 1 = i)
    (hF : IsZero (F.homology i)) (γ : A ⟶ F.X i) (hγ : γ ≫ F.d i (i + 1) = 0) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ h : (restrictModules X U).obj A ⟶ (restrictModules X U).obj (F.X j),
        h ≫ (restrictModules X U).map (F.d j i) = (restrictModules X U).map γ := by
  have : Epi (F.toCycles j i) := epi_toCycles_of_isZero_homology hij hF
  obtain ⟨U, hxU, l, hl⟩ := exists_local_lift_of_isDirectSummandOfFiniteFree
    (F.liftCycles γ (i + 1) (by simp) hγ) (F.toCycles j i) hA x
  refine ⟨U, hxU, l, ?_⟩
  calc l ≫ (restrictModules X U).map (F.d j i)
      = (l ≫ (restrictModules X U).map (F.toCycles j i)) ≫
          (restrictModules X U).map (F.iCycles i) := by
        rw [← F.toCycles_i j i, (restrictModules X U).map_comp, Category.assoc]
    _ = (restrictModules X U).map (F.liftCycles γ (i + 1) (by simp) hγ) ≫
          (restrictModules X U).map (F.iCycles i) := by rw [hl]
    _ = (restrictModules X U).map γ := by
        rw [← (restrictModules X U).map_comp, F.liftCycles_i]

end AlgebraicGeometry.RingedSpace

end
