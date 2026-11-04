module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The principal divisor of a rational function

Let `X` be a locally Noetherian integral scheme and let `f` be a rational function on `X`, that
is, an element of the function field `R(X) = O_{X,η}` at the generic point. For a prime divisor
`Z ⊆ X` — an integral closed subscheme of codimension one, equivalently a point `ξ` of `X` with
`Order.coheight ξ = 1` — the order of vanishing `ord_Z(f)` is the order of `f` in the local ring
`O_{X,ξ}`, which is Mathlib's `AlgebraicGeometry.Scheme.ord`. The principal divisor of `f` is
the formal sum `div(f) = ∑_Z ord_Z(f) [Z]`.

Stacks 02RL, the substance of this file, says that two collections of prime divisors attached to
`f` are locally finite in `X`: those at whose generic point `ξ` the function `f` fails to lie in
the local ring `O_{X,ξ}`, and those along which `f` has nonzero order. The second is what makes
`div(f)` a divisor at all. Both proofs are the one in the Stacks Project. Every rational function
is the germ of a section of `O_X` on some nonempty open `U`, hence lies in `O_{X,z}` for every
`z ∈ U`; and a nonzero one is a *unit* section on some nonempty affine open `U` (Mathlib's
`exists_isUnit_germ_eq`), so its order vanishes at every point of `U`. Either way the collection
is supported in the closed set `X \ U`. On a Noetherian open subscheme `V` the closed set
`V \ U` is a finite union of irreducible closed sets, and a point of codimension one outside `U`
has its closure *maximal* among the irreducible closed subsets of `V \ U` — otherwise a strictly
larger one would interpose a point between it and the generic point of `V`, making its
codimension at least two. So the closure of such a point is one of the finitely many pieces, and
there are only finitely many such points in `V`.

Mathlib indexes an integral closed subscheme of `X` by its generic point, so `div(f)` is
recorded here as an `AlgebraicGeometry.AlgebraicCycle X ℤ`, i.e. a locally finitely supported
function on the points of `X`; it is supported on the points of codimension one, which are the
prime divisors. The passage between local finiteness of the support and local finiteness of the
family of closed subschemes is `Stacks.Chow.locallyFinite_closure_singleton_iff`.

## Main definitions

* `Stacks.Chow.principalCycle` — the principal divisor `div(f)` of a rational function, as an
  algebraic cycle (Stacks 0BE3).

## Main results

* `Stacks.Chow.finite_notMem_coheight_eq_one` — on a Noetherian irreducible scheme there are
  only finitely many points of codimension one outside a given nonempty open set.
* `Stacks.Chow.locallyFinite_closure_notMem_range_algebraMap` — the prime divisors at whose
  generic point a rational function does not lie in the local ring form a locally finite
  collection (Stacks 02RL).
* `Stacks.Chow.locallyFiniteSupport_ord` — the prime divisors along which a rational function
  has nonzero order form a locally finite collection (Stacks 02RL).
* `Stacks.Chow.principalCycle_apply` — the coefficient of `div(f)` is the order of vanishing.
* `Stacks.Chow.principalCycle_mul` — `div(fg) = div(f) + div(g)` (Stacks 02RP).

## References

* [Stacks Project, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Codimension-one points outside an open set -/

/-- On a Noetherian irreducible scheme only finitely many points of codimension one lie outside
a given nonempty open subscheme `U`. Indeed `X \ U` is a finite union of irreducible closed
sets, and the closure of a codimension-one point `z ∉ U` is maximal among the irreducible closed
subsets of `X \ U`: a strictly larger one would have a generic point strictly between `z` and
the generic point of `X`, forcing the codimension of `z` to be at least two. So that closure is
one of the finitely many pieces, and `z` is recovered from it. -/
theorem finite_notMem_coheight_eq_one {X : Scheme.{u}} [IrreducibleSpace X] [NoetherianSpace X]
    (U : X.Opens) [Nonempty U] :
    {z : X | z ∉ U ∧ coheight z = 1}.Finite := by
  -- the specialization preorder on the points of a scheme is a partial order
  have hlt : ∀ {a b : X}, a ≤ b → a ≠ b → a < b := fun hab hne ↦
    lt_iff_le_not_ge.mpr ⟨hab, fun h ↦ hne (Specializes.antisymm h hab).eq⟩
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irr, h𝒮cover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (α := X) (s := (U : Set X)ᶜ)
      U.isOpen.isClosed_compl
  lift 𝒮 to Finset (Set X) using h𝒮fin
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have key : ∀ z : X, z ∉ U → coheight z = 1 → closure ({z} : Set X) ∈ 𝒮 := by
    intro z hzU hzc
    have hcl : closure ({z} : Set X) ⊆ ⋃₀ (𝒮 : Set (Set X)) := by
      rw [← h𝒮cover]
      exact closure_minimal (Set.singleton_subset_iff.mpr hzU) U.isOpen.isClosed_compl
    obtain ⟨t, htS, hzt⟩ := isIrreducible_iff_sUnion_isClosed.mp
      isIrreducible_singleton.closure 𝒮 (fun s hs ↦ h𝒮closed s hs) hcl
    set τ := (h𝒮irr t htS).genericPoint with hτdef
    have hgen : closure ({τ} : Set X) = t :=
      (h𝒮irr t htS).isGenericPoint_genericPoint (h𝒮closed t htS)
    have hτt : τ ∈ t := by rw [← hgen]; exact subset_closure (Set.mem_singleton τ)
    have hτU : τ ∉ U := by
      have hsub : t ⊆ (U : Set X)ᶜ := by
        rw [h𝒮cover]
        exact Set.subset_sUnion_of_mem htS
      exact hsub hτt
    have hτη : τ < genericPoint X :=
      hlt (genericPoint_specializes τ) fun h ↦ hτU (by rw [h]; exact hηU)
    have hone : (1 : ℕ∞) ≤ coheight τ := le_trans le_add_self (coheight_add_one_le hτη)
    have hzmem : z ∈ closure ({τ} : Set X) := by
      rw [hgen]
      exact hzt (subset_closure (Set.mem_singleton z))
    have hzτ : z ≤ τ := specializes_iff_mem_closure.mpr hzmem
    have hz : z = τ := by
      by_contra hne
      have hstep := coheight_add_one_le (hlt hzτ hne)
      rw [hzc] at hstep
      -- `coheight τ + 1 ≤ 1` is incompatible with `1 ≤ coheight τ`
      have habs : (2 : ℕ∞) ≤ 1 := by
        refine le_trans ?_ hstep
        rw [show (2 : ℕ∞) = 1 + 1 from rfl]
        gcongr
      exact absurd habs (by decide)
    rw [hz, hgen]
    exact htS
  refine Set.Finite.of_finite_image (f := fun z ↦ closure ({z} : Set X))
    (𝒮.finite_toSet.subset ?_) ?_
  · rintro - ⟨z, ⟨hzU, hzc⟩, rfl⟩
    exact key z hzU hzc
  · intro a _ b _ hab
    exact (show IsGenericPoint a (closure ({b} : Set X)) from hab).eq isGenericPoint_closure

/-! ### Local finiteness of the prime divisors of a rational function -/

/-- Around every point `x` of a locally Noetherian integral scheme there is a neighbourhood `V`
containing only finitely many codimension-one points outside a given nonempty open set `U`. -/
private theorem exists_mem_nhds_finite_notMem_coheight_eq_one (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (x : X) (U : X.Opens) [Nonempty U] :
    ∃ V ∈ nhds x, {z : X | z ∈ V ∧ z ∉ U ∧ coheight z = 1}.Finite := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨(V : Set X), V.isOpen.mem_nhds hxV, ?_⟩
  -- transfer the counting problem to the Noetherian open subscheme `V`
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace V.toScheme := noetherianSpace_of_isAffineOpen V hV
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have : Nonempty (V.ι ⁻¹ᵁ U) := ⟨⟨⟨genericPoint X, hηV⟩, hηU⟩⟩
  refine ((finite_notMem_coheight_eq_one (X := V.toScheme) (V.ι ⁻¹ᵁ U)).image
    (fun w ↦ (V.ι.base w : X))).subset ?_
  rintro z ⟨hzV, hzU, hzc⟩
  obtain ⟨w, hw⟩ : ∃ w : ↥V.toScheme, V.ι.base w = z := ⟨⟨z, hzV⟩, rfl⟩
  have hco : coheight (V.ι.base w) = coheight w := coheight_eq_of_isOpenImmersion V.ι
  subst hw
  exact ⟨w, ⟨hzU, hco ▸ hzc⟩, rfl⟩

/-- **Stacks 02RL.** On a locally Noetherian integral scheme the prime divisors at whose generic
point `ξ` a rational function `f` does not lie in the local ring `O_{X,ξ}` form a locally finite
collection of closed subsets of `X`. A prime divisor is indexed by its generic point, so the
collection is the family of closures of the codimension-one points `z` with `f ∉ O_{X,z}`. -/
@[stacks 02RL "the prime divisors with f ∉ O_{X,ξ}; no hypothesis f ≠ 0 needed"]
theorem locallyFinite_closure_notMem_range_algebraMap (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (f : X.functionField) :
    LocallyFinite fun z : {z : X // coheight z = 1 ∧
        f ∉ Set.range (algebraMap (X.presheaf.stalk z) X.functionField)} ↦
      closure ({(z : X)} : Set X) := by
  refine (locallyFinite_closure_singleton_iff _).mpr fun x ↦ ?_
  -- `f` is the germ of a section on an open `U`, hence lies in `O_{X,z}` for every `z ∈ U`.
  obtain ⟨U, hηU, g, hg⟩ := X.presheaf.exists_germ_eq f
  have : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  have hmemU : ∀ z ∈ U, f ∈ Set.range (algebraMap (X.presheaf.stalk z) X.functionField) :=
    fun z hz ↦ ⟨X.presheaf.germ U z hz g, by
      rw [X.algebraMap_germ_eq_germToFunctionField hz g]; exact hg⟩
  obtain ⟨V, hV, hfin⟩ := exists_mem_nhds_finite_notMem_coheight_eq_one X x U
  refine ⟨V, hV, Set.Finite.of_finite_image (hfin.subset ?_) Subtype.val_injective.injOn⟩
  rintro - ⟨⟨z, hzc, hzf⟩, hzV, rfl⟩
  exact ⟨hzV, fun h ↦ hzf (hmemU z h), hzc⟩

/-- **Stacks 02RL.** On a locally Noetherian integral scheme the prime divisors along which a
rational function `f` has nonzero order form a locally finite collection: the support of
`z ↦ ord_z(f)` meets a neighbourhood of every point in a finite set. -/
@[stacks 02RL "the prime divisors with ord_Z(f) ≠ 0"]
theorem locallyFiniteSupport_ord (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : LocallyFiniteSupport (X.ord f) := by
  intro x
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨Set.univ, Filter.univ_mem, by simp⟩
  -- `f` is a unit section on a nonempty affine open `U`, so its order vanishes on `U`.
  obtain ⟨U, hU, f', hUne, hgerm, hunit⟩ := exists_isUnit_germ_eq X f hf
  have hordU : ∀ z : X, z ∈ U → X.ord f z = 0 := fun z hz ↦ by
    rw [← hgerm]; exact X.ord_of_isUnit hunit hz
  obtain ⟨V, hV, hfin⟩ := exists_mem_nhds_finite_notMem_coheight_eq_one X x U
  refine ⟨V, hV, hfin.subset ?_⟩
  rintro z ⟨hzV, hz⟩
  exact ⟨hzV, fun h ↦ hz (hordU z h), by
    by_contra hne
    exact hz (X.ord_eq_zero_of_coheight_neq_one hne f)⟩

/-! ### The principal divisor -/

/-- **Stacks 0BE3.** The principal divisor `div(f) = ∑_Z ord_Z(f) [Z]` of a rational function on
a locally Noetherian integral scheme, as an algebraic cycle: the integral closed subscheme
`closure {z}` is indexed by its generic point `z`, and carries the coefficient `ord_z(f)`. Local
finiteness of the family of prime divisors involved is Stacks 02RL. -/
@[stacks 0BE3, ega "IV 21.6.7" "partial"]
def principalCycle (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : AlgebraicCycle X ℤ where
  toFun := X.ord f
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := locallyFiniteSupport_ord X f z

/-- The coefficient of the principal divisor of `f` at a point is the order of vanishing of `f`
there. -/
@[simp]
theorem principalCycle_apply (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (z : X) : principalCycle X f z = X.ord f z :=
  rfl

/-- The principal divisor of `0` — a junk value, since `0` is not a rational function in the
sense of Stacks 0BE3 — is the zero cycle. -/
@[simp]
theorem principalCycle_zero (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    principalCycle X 0 = 0 := by
  apply Function.locallyFinsuppWithin.ext
  simp

/-- **Stacks 02RP.** The principal divisor of a product of nonzero rational functions is the sum
of the principal divisors. -/
@[stacks 02RP, ega "IV 21.1.3" "(21.1.3.1)"]
theorem principalCycle_mul (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    principalCycle X (f * g) = principalCycle X f + principalCycle X g := by
  apply Function.locallyFinsuppWithin.ext
  intro z
  simpa using X.ord_mul hf hg

end Stacks.Chow
