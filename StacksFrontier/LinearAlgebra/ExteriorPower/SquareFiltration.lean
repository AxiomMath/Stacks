module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.LinearAlgebra.ExteriorPower.DivisibleRetraction
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The filtration of the exterior square along a split injection

Let `A` be a commutative ring and `0 → P' →u P →v P'' → 0` a short exact sequence of `A`-modules.
The exterior square `⋀² P` carries the submodule `Fil ⊆ ⋀² P` spanned by the wedges `u p' ∧ p`,
the image of the wedge map `P' ⊗ P → ⋀² P`, `p' ⊗ p ↦ u p' ∧ p`. It sits in two sequences

`0 → ⋀² P' → Fil → P' ⊗ P'' → 0` and `0 → Fil → ⋀² P → ⋀² P'' → 0`,

whose maps are `⋀² u`, the map `u p' ∧ p ↦ p' ⊗ v p`, the inclusion and `⋀² v`. The second is
exact as soon as `v` is surjective with kernel `u(P')`: this is the presentation of exterior
powers of Stacks 01CJ (`exterior_power_presentation`) in degree two. The first is exact when the
sequence is split. The map `u p' ∧ p ↦ p' ⊗ v p` is well defined once `u` has a retraction `r`:
it is then the restriction to `Fil` of the alternating map `p ∧ q ↦ r p ⊗ v q - r q ⊗ v p`,
because `v ∘ u = 0`. Being determined by its values on generators, it does not depend on `r`.
Exactness in the middle needs only the right exactness of `P' ⊗ -`: an element of `P' ⊗ P` killed
by `P' ⊗ v` comes from `P' ⊗ P'`, and the wedge map sends `P' ⊗ P'` into `⋀² P'`. Finally `⋀² u`
is injective because `⋀² r` is a retraction of it.

All maps are canonical and natural in morphisms of sequences, so the construction applies
objectwise to a short exact sequence of diagrams of modules — for instance of simplicial modules
— which is objectwise split, with splittings not compatible with the transition maps, and gives
two short exact sequences of diagrams of modules.

## Main definitions

* `Stacks.ExteriorSquare.wedgeLeft`: the wedge map `P' ⊗ P → ⋀² P`, `p' ⊗ p ↦ u p' ∧ p`.
* `Stacks.ExteriorSquare.filtration`: its image `Fil`.
* `Stacks.ExteriorSquare.toFiltration`: `⋀² u : ⋀² P' → Fil`.
* `Stacks.ExteriorSquare.filtrationToTensor`: the canonical map `Fil → P' ⊗ P''`,
  `u p' ∧ p ↦ p' ⊗ v p`.
* `Stacks.ExteriorSquare.filtrationQuotientEquiv`: `Fil / ⋀² P' ≃ P' ⊗ P''`.
* `Stacks.ExteriorSquare.filtrationMap`: the map `Fil → Fil` induced by a commutative square.
* `Stacks.ExteriorSquare.filtrationFunctor`, `Stacks.ExteriorSquare.filtrationShortComplex`,
  `Stacks.ExteriorSquare.exteriorSquareShortComplex`: the same constructions for a short complex
  `X₁ → X₂ → X₃` of functors `J ⥤ ModuleCat A`, giving the short complexes
  `⋀² X₁ → Fil → X₁ ⊗ X₃` and `Fil → ⋀² X₂ → ⋀² X₃`.

## Main results

* `Stacks.ExteriorSquare.toFiltration_injective`,
  `Stacks.ExteriorSquare.exact_toFiltration_filtrationToTensor`,
  `Stacks.ExteriorSquare.filtrationToTensor_surjective`: `0 → ⋀² P' → Fil → P' ⊗ P'' → 0` is
  exact for a split short exact sequence.
* `Stacks.ExteriorSquare.ker_map_eq_filtration`, `Stacks.ExteriorSquare.exact_subtype_map`:
  `0 → Fil → ⋀² P → ⋀² P'' → 0` is exact as soon as `v` is surjective with kernel `u(P')`.
* `Stacks.ExteriorSquare.filtrationMap_comp_toFiltration`,
  `Stacks.ExteriorSquare.filtrationToTensor_comp_filtrationMap`,
  `Stacks.ExteriorSquare.subtype_comp_filtrationMap`: naturality.
* `Stacks.ExteriorSquare.filtrationShortComplex_shortExact`,
  `Stacks.ExteriorSquare.exteriorSquareShortComplex_shortExact`: the two short exact sequences of
  diagrams of modules, e.g. of simplicial modules.
* `exteriorPower.map_smul_eq_pow_smul` (and the existing `exteriorPower.map_smul_id` of
  `DivisibleRetraction.lean`): `⋀ⁿ (c • f) = cⁿ • ⋀ⁿ f`,
  so in particular `⋀² (c • id) = c² • id`.

## Implementation notes

The splitting enters only as the hypothesis that a retraction of `u` exists, an argument of type
`Prop`; the map `Fil → P' ⊗ P''` is defined by descending `P' ⊗ v` along the surjection
`P' ⊗ P → Fil`, so no choice is made. For diagrams of modules the hypothesis is that each
component of `X₁ → X₂` is a split monomorphism. A simplicial module is a functor
`SimplexCategoryᵒᵖ ⥤ ModuleCat A`, so the statements for diagrams apply to it verbatim.

## References

* [Stacks, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public section

open scoped TensorProduct

namespace exteriorPower

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
  [Module A N]

/-- The `n`-th exterior power of `c • f` is `c ^ n` times the `n`-th exterior power of `f`. -/
theorem map_smul_eq_pow_smul (n : ℕ) (c : A) (f : M →ₗ[A] N) :
    map n (c • f) = c ^ n • map n f := by
  refine linearMap_ext (AlternatingMap.ext fun m => ?_)
  simp only [LinearMap.compAlternatingMap_apply, map_apply_ιMulti, LinearMap.smul_apply]
  have : (⇑(c • f) ∘ m) = fun i => c • (f ∘ m) i := by
    ext i
    simp
  rw [this, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end exteriorPower

namespace Stacks.ExteriorSquare

variable {A : Type*} [CommRing A]
  {P' P P'' : Type*} [AddCommGroup P'] [Module A P'] [AddCommGroup P] [Module A P]
  [AddCommGroup P''] [Module A P'']

/-! ### The wedge map and the filtration -/

/-- The wedge map `P' ⊗ P → ⋀² P`, `p' ⊗ p ↦ u p' ∧ p`. -/
noncomputable def wedgeLeft (u : P' →ₗ[A] P) : P' ⊗[A] P →ₗ[A] ⋀[A]^2 P :=
  ExtPow.beta 1 u ∘ₗ (exteriorPower.oneEquiv A P).symm.toLinearMap.lTensor P'

/-- The defining formula of the wedge map. -/
theorem wedgeLeft_tmul (u : P' →ₗ[A] P) (p' : P') (p : P) :
    wedgeLeft u (p' ⊗ₜ p) = exteriorPower.ιMulti A 2 ![u p', p] := by
  apply Subtype.ext
  simp [wedgeLeft, ExtPow.beta_tmul, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]

/-- The image of `wedgeLeft u`: the submodule `Fil` of `⋀² P` spanned by the wedges
`u p' ∧ p`. -/
@[sga "6 V 2.2.1" "special case"]
noncomputable abbrev filtration (u : P' →ₗ[A] P) : Submodule A (⋀[A]^2 P) :=
  LinearMap.range (wedgeLeft u)

/-- The values of the wedge map lie in `Fil`. -/
theorem wedgeLeft_mem_filtration (u : P' →ₗ[A] P) (x : P' ⊗[A] P) :
    wedgeLeft u x ∈ filtration u :=
  LinearMap.mem_range_self _ x

/-- The generators `u p' ∧ p` lie in `Fil`. -/
theorem ιMulti_mem_filtration (u : P' →ₗ[A] P) (p' : P') (p : P) :
    exteriorPower.ιMulti A 2 ![u p', p] ∈ filtration u :=
  wedgeLeft_tmul u p' p ▸ wedgeLeft_mem_filtration u _

/-- `Fil` is the submodule spanned by the wedges `u p' ∧ p`. -/
theorem filtration_eq_span (u : P' →ₗ[A] P) :
    filtration u =
      Submodule.span A (Set.range fun x : P' × P => exteriorPower.ιMulti A 2 ![u x.1, x.2]) := by
  rw [filtration, LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨_, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨a, b, (wedgeLeft_tmul u a b).symm⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a ⊗ₜ b, ⟨a, b, rfl⟩, wedgeLeft_tmul u a b⟩

/-- For the identity, the wedge map `P ⊗ P → ⋀² P` is surjective. -/
theorem wedgeLeft_id_surjective :
    Function.Surjective (wedgeLeft (LinearMap.id : P →ₗ[A] P)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  refine ⟨m 0 ⊗ₜ m 1, ?_⟩
  rw [wedgeLeft_tmul]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- `⋀² f₂` sends the wedge `u₁ a ∧ b` to `u₂ (f₁ a) ∧ f₂ b` when `f₂ ∘ u₁ = u₂ ∘ f₁`. -/
private theorem map_ιMulti_two {Q' Q : Type*} [AddCommGroup Q'] [Module A Q'] [AddCommGroup Q]
    [Module A Q] {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q') (f₂ : P →ₗ[A] Q)
    (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) (a : P') (b : P) :
    exteriorPower.map 2 f₂ (exteriorPower.ιMulti A 2 ![u₁ a, b]) =
      exteriorPower.ιMulti A 2 ![u₂ (f₁ a), f₂ b] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i
  · exact LinearMap.congr_fun h a
  · rfl

/-- Naturality of the wedge map: for `f₂ ∘ u₁ = u₂ ∘ f₁`, the square formed by the wedge maps,
`f₁ ⊗ f₂` and `⋀² f₂` commutes. -/
theorem map_comp_wedgeLeft {Q' Q : Type*} [AddCommGroup Q'] [Module A Q'] [AddCommGroup Q]
    [Module A Q] {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q') (f₂ : P →ₗ[A] Q)
    (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) :
    exteriorPower.map 2 f₂ ∘ₗ wedgeLeft u₁ = wedgeLeft u₂ ∘ₗ TensorProduct.map f₁ f₂ := by
  refine TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, wedgeLeft_tmul, TensorProduct.map_tmul]
  exact map_ιMulti_two f₁ f₂ h a b

/-- `wedgeLeft u ∘ (P' ⊗ u) = ⋀² u ∘ wedgeLeft id`. -/
theorem wedgeLeft_comp_lTensor (u : P' →ₗ[A] P) :
    wedgeLeft u ∘ₗ u.lTensor P' = exteriorPower.map 2 u ∘ₗ wedgeLeft LinearMap.id := by
  rw [map_comp_wedgeLeft (u₁ := LinearMap.id) LinearMap.id u (by rfl)]
  rfl

/-- The image of `⋀² u` lies in `Fil`. -/
theorem range_map_le_filtration (u : P' →ₗ[A] P) :
    LinearMap.range (exteriorPower.map 2 u) ≤ filtration u := by
  rw [← LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr wedgeLeft_id_surjective), ← wedgeLeft_comp_lTensor]
  exact LinearMap.range_comp_le_range _ _

/-! ### The first short exact sequence `0 → ⋀² P' → Fil → P' ⊗ P'' → 0` -/

/-- The map `⋀² u : ⋀² P' → ⋀² P`, with codomain restricted to `Fil`. -/
noncomputable def toFiltration (u : P' →ₗ[A] P) : ⋀[A]^2 P' →ₗ[A] filtration u :=
  (exteriorPower.map 2 u).codRestrict (filtration u)
    fun x => range_map_le_filtration u (LinearMap.mem_range_self _ x)

/-- `toFiltration u` is `⋀² u` followed by the inclusion of `Fil`. -/
@[simp]
theorem coe_toFiltration (u : P' →ₗ[A] P) (x : ⋀[A]^2 P') :
    (toFiltration u x : ⋀[A]^2 P) = exteriorPower.map 2 u x :=
  rfl

/-- `toFiltration u` composed with the inclusion of `Fil` is `⋀² u`. -/
theorem subtype_comp_toFiltration (u : P' →ₗ[A] P) :
    (filtration u).subtype ∘ₗ toFiltration u = exteriorPower.map 2 u :=
  rfl

/-- On wedges `a ∧ b` of `⋀² P'`, `toFiltration u` is the wedge map applied to `a ⊗ u b`. -/
theorem toFiltration_comp_wedgeLeft (u : P' →ₗ[A] P) :
    toFiltration u ∘ₗ wedgeLeft LinearMap.id = (wedgeLeft u).rangeRestrict ∘ₗ u.lTensor P' :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (wedgeLeft_comp_lTensor u) x).symm

/-- If `u` has a retraction, `⋀² u` is injective. -/
theorem toFiltration_injective {u : P' →ₗ[A] P} (hr : ∃ r : P →ₗ[A] P', r ∘ₗ u = LinearMap.id) :
    Function.Injective (toFiltration u) := by
  obtain ⟨r, hr⟩ := hr
  exact fun _ _ hxy => exteriorPower.map_injective r hr (congrArg Subtype.val hxy)

/-- Given a retraction `r` of `u`, the alternating map `(p, q) ↦ r p ⊗ v q - r q ⊗ v p`. -/
private noncomputable def crossAlternating (r : P →ₗ[A] P') (v : P →ₗ[A] P'') :
    P [⋀^Fin 2]→ₗ[A] P' ⊗[A] P'' where
  toFun m := r (m 0) ⊗ₜ v (m 1) - r (m 1) ⊗ₜ v (m 0)
  map_update_add' m i x y := by
    fin_cases i <;>
      simp [TensorProduct.add_tmul, TensorProduct.tmul_add] <;> abel
  map_update_smul' m i c x := by
    fin_cases i <;>
      simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_sub]
  map_eq_zero_of_eq' m i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

private theorem crossAlternating_apply (r : P →ₗ[A] P') (v : P →ₗ[A] P'') (m : Fin 2 → P) :
    crossAlternating r v m = r (m 0) ⊗ₜ v (m 1) - r (m 1) ⊗ₜ v (m 0) :=
  rfl

/-- If `u` has a retraction and `v ∘ u = 0`, every relation among the generators `u p' ∧ p` of
`Fil` is a relation among the `p' ⊗ v p`. -/
theorem ker_wedgeLeft_le {u : P' →ₗ[A] P} {v : P →ₗ[A] P''}
    (hr : ∃ r : P →ₗ[A] P', r ∘ₗ u = LinearMap.id) (hvu : v ∘ₗ u = 0) :
    LinearMap.ker (wedgeLeft u) ≤ LinearMap.ker (v.lTensor P') := by
  obtain ⟨r, hr⟩ := hr
  have key : exteriorPower.alternatingMapLinearEquiv (crossAlternating r v) ∘ₗ wedgeLeft u =
      v.lTensor P' := by
    refine TensorProduct.ext' fun a b => ?_
    have h1 : r (u a) = a := LinearMap.congr_fun hr a
    have h2 : v (u a) = 0 := LinearMap.congr_fun hvu a
    simp [wedgeLeft_tmul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      crossAlternating_apply, h1, h2]
  rw [← key]
  exact LinearMap.ker_le_ker_comp _ _

/-- **The canonical map `Fil → P' ⊗ P''`**, `u p' ∧ p ↦ p' ⊗ v p`. It is defined by
descending `P' ⊗ v : P' ⊗ P → P' ⊗ P''` along the surjection `wedgeLeft u : P' ⊗ P → Fil`, which
is possible as soon as `u` has a retraction and `v ∘ u = 0`; it does not depend on a choice of
retraction. -/
noncomputable def filtrationToTensor (u : P' →ₗ[A] P) (v : P →ₗ[A] P'')
    (hr : ∃ r : P →ₗ[A] P', r ∘ₗ u = LinearMap.id) (hvu : v ∘ₗ u = 0) :
    filtration u →ₗ[A] P' ⊗[A] P'' :=
  (LinearMap.ker (wedgeLeft u)).liftQ (v.lTensor P') (ker_wedgeLeft_le hr hvu) ∘ₗ
    (wedgeLeft u).quotKerEquivRange.symm.toLinearMap

section filtrationToTensor

variable {u : P' →ₗ[A] P} {v : P →ₗ[A] P''}
  (hr : ∃ r : P →ₗ[A] P', r ∘ₗ u = LinearMap.id) (hvu : v ∘ₗ u = 0)

/-- `Fil → P' ⊗ P''` composed with the surjection `P' ⊗ P → Fil` is `P' ⊗ v`. -/
theorem filtrationToTensor_comp_rangeRestrict :
    filtrationToTensor u v hr hvu ∘ₗ (wedgeLeft u).rangeRestrict = v.lTensor P' := by
  refine LinearMap.ext fun x => ?_
  simp only [filtrationToTensor, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show (wedgeLeft u).rangeRestrict x = ⟨wedgeLeft u x, LinearMap.mem_range_self _ x⟩ from rfl,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- `Fil → P' ⊗ P''` sends the image of `x : P' ⊗ P` under the wedge map to `(P' ⊗ v) x`. -/
theorem filtrationToTensor_apply_wedgeLeft (x : P' ⊗[A] P) :
    filtrationToTensor u v hr hvu ⟨wedgeLeft u x, wedgeLeft_mem_filtration u x⟩ =
      v.lTensor P' x :=
  LinearMap.congr_fun (filtrationToTensor_comp_rangeRestrict hr hvu) x

/-- The defining formula `u p' ∧ p ↦ p' ⊗ v p`. -/
@[simp]
theorem filtrationToTensor_apply_ιMulti (p' : P') (p : P) :
    filtrationToTensor u v hr hvu ⟨exteriorPower.ιMulti A 2 ![u p', p],
      ιMulti_mem_filtration u p' p⟩ = p' ⊗ₜ v p := by
  simpa only [wedgeLeft_tmul, LinearMap.lTensor_tmul] using
    filtrationToTensor_apply_wedgeLeft hr hvu (p' ⊗ₜ p)

end filtrationToTensor

/-- Two linear maps out of `Fil` agree as soon as they agree on the generators `u p' ∧ p`. -/
theorem filtration_hom_ext {M : Type*} [AddCommGroup M] [Module A M] {u : P' →ₗ[A] P}
    {f g : filtration u →ₗ[A] M}
    (h : ∀ (p' : P') (p : P),
      f ⟨exteriorPower.ιMulti A 2 ![u p', p], ιMulti_mem_filtration u p' p⟩ =
        g ⟨exteriorPower.ιMulti A 2 ![u p', p], ιMulti_mem_filtration u p' p⟩) :
    f = g := by
  have hs : Function.Surjective (wedgeLeft u).rangeRestrict := LinearMap.surjective_rangeRestrict _
  refine (LinearMap.cancel_right hs).mp (TensorProduct.ext' fun a b => ?_)
  have e : (wedgeLeft u).rangeRestrict (a ⊗ₜ b) =
      ⟨exteriorPower.ιMulti A 2 ![u a, b], ιMulti_mem_filtration u a b⟩ :=
    Subtype.ext (wedgeLeft_tmul u a b)
  simp only [LinearMap.comp_apply, e, h]

section exact

variable {u : P' →ₗ[A] P} {v : P →ₗ[A] P''}
  (hr : ∃ r : P →ₗ[A] P', r ∘ₗ u = LinearMap.id) (hvu : v ∘ₗ u = 0)

/-- The composite `⋀² P' → Fil → P' ⊗ P''` vanishes. -/
theorem filtrationToTensor_comp_toFiltration :
    filtrationToTensor u v hr hvu ∘ₗ toFiltration u = 0 := by
  refine (LinearMap.cancel_right (wedgeLeft_id_surjective (A := A) (P := P'))).mp ?_
  rw [LinearMap.comp_assoc, toFiltration_comp_wedgeLeft, ← LinearMap.comp_assoc,
    filtrationToTensor_comp_rangeRestrict, ← LinearMap.lTensor_comp, hvu, LinearMap.lTensor_zero,
    LinearMap.zero_comp]

/-- If `v` is surjective, so is `Fil → P' ⊗ P''`. -/
theorem filtrationToTensor_surjective (hv : Function.Surjective v) :
    Function.Surjective (filtrationToTensor u v hr hvu) := by
  have h := LinearMap.lTensor_surjective P' hv
  rw [← filtrationToTensor_comp_rangeRestrict hr hvu, LinearMap.coe_comp] at h
  exact h.of_comp

/-- **Exactness of `⋀² P' → Fil → P' ⊗ P''` in the middle.** Only the right exactness of
`P' ⊗ -` is used: the hypotheses are that `u, v` is exact at `P` and that `v` is surjective. -/
theorem exact_toFiltration_filtrationToTensor (h : Function.Exact u v)
    (hv : Function.Surjective v) :
    Function.Exact (toFiltration u) (filtrationToTensor u v hr hvu) := by
  intro y
  obtain ⟨x, rfl⟩ := (LinearMap.surjective_rangeRestrict (wedgeLeft u)) y
  rw [← LinearMap.comp_apply (filtrationToTensor u v hr hvu),
    filtrationToTensor_comp_rangeRestrict]
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (lTensor_exact P' h hv x).mp hx
    exact ⟨wedgeLeft LinearMap.id z, LinearMap.congr_fun (toFiltration_comp_wedgeLeft u) z⟩
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := wedgeLeft_id_surjective w
    have := LinearMap.congr_fun (filtrationToTensor_comp_toFiltration hr hvu) (wedgeLeft .id z)
    rwa [LinearMap.comp_apply, hw, ← LinearMap.comp_apply (filtrationToTensor u v hr hvu),
      filtrationToTensor_comp_rangeRestrict] at this

/-- **`Fil / ⋀² P' ≅ P' ⊗ P''`**, the isomorphism induced by `u p' ∧ p ↦ p' ⊗ v p`, for a split
short exact sequence `0 → P' → P → P'' → 0`. -/
@[sga "6 V 2.2.1" "special case"]
noncomputable def filtrationQuotientEquiv (h : Function.Exact u v) (hv : Function.Surjective v) :
    (filtration u ⧸ LinearMap.range (toFiltration u)) ≃ₗ[A] P' ⊗[A] P'' :=
  (exact_toFiltration_filtrationToTensor hr hvu h hv).linearEquivOfSurjective
    (filtrationToTensor_surjective hr hvu hv)

/-- `filtrationQuotientEquiv` is induced by `filtrationToTensor`. -/
@[simp]
theorem filtrationQuotientEquiv_mk (h : Function.Exact u v) (hv : Function.Surjective v)
    (x : filtration u) :
    filtrationQuotientEquiv hr hvu h hv (Submodule.Quotient.mk x) =
      filtrationToTensor u v hr hvu x :=
  rfl

end exact

/-! ### The second short exact sequence `0 → Fil → ⋀² P → ⋀² P'' → 0` -/

/-- `Fil` is the image of the map `P' ⊗ ⋀¹ P → ⋀² P` of Stacks 01CJ. -/
theorem filtration_eq_range_beta (u : P' →ₗ[A] P) :
    filtration u = LinearMap.range (ExtPow.beta 1 u) :=
  LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (LinearMap.lTensor_surjective P' (exteriorPower.oneEquiv A P).symm.surjective))

/-- If `v ∘ u = 0`, then `⋀² v` vanishes on `Fil`. -/
theorem filtration_le_ker_map {u : P' →ₗ[A] P} {v : P →ₗ[A] P''} (hvu : v ∘ₗ u = 0) :
    filtration u ≤ LinearMap.ker (exteriorPower.map 2 v) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
    map_comp_wedgeLeft (u₂ := (0 : P' →ₗ[A] P'')) LinearMap.id v (by rw [hvu]; rfl)]
  have : wedgeLeft (0 : P' →ₗ[A] P'') = 0 := TensorProduct.ext' fun a b => by
    rw [wedgeLeft_tmul, LinearMap.zero_apply, LinearMap.zero_apply]
    exact (exteriorPower.ιMulti A 2).map_coord_zero 0 rfl
  rw [this, LinearMap.zero_comp, LinearMap.zero_apply]

/-- **The kernel of `⋀² v` is `Fil`** when `v` is surjective with kernel the image of `u`
(Stacks 01CJ in degree two); no splitting is needed. -/
theorem ker_map_eq_filtration {u : P' →ₗ[A] P} {v : P →ₗ[A] P''} (h : Function.Exact u v)
    (hv : Function.Surjective v) :
    LinearMap.ker (exteriorPower.map 2 v) = filtration u :=
  ((exterior_power_presentation u v hv h.linearMap_ker_eq.symm 1).2.symm.trans
    (filtration_eq_range_beta u).symm :)

/-- **Exactness of `0 → Fil → ⋀² P → ⋀² P'' → 0` in the middle.** -/
theorem exact_subtype_map {u : P' →ₗ[A] P} {v : P →ₗ[A] P''} (h : Function.Exact u v)
    (hv : Function.Surjective v) :
    Function.Exact (filtration u).subtype (exteriorPower.map 2 v) := by
  intro x
  rw [← LinearMap.mem_ker, ker_map_eq_filtration h hv]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

/-! ### Naturality -/

section naturality

variable {Q' Q Q'' R' R R'' : Type*} [AddCommGroup Q'] [Module A Q'] [AddCommGroup Q] [Module A Q]
  [AddCommGroup Q''] [Module A Q''] [AddCommGroup R'] [Module A R'] [AddCommGroup R] [Module A R]
  [AddCommGroup R''] [Module A R'']

/-- `⋀² f₂` maps `Fil(u₁)` into `Fil(u₂)` when `f₂ ∘ u₁ = u₂ ∘ f₁`. -/
theorem map_mem_filtration {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q')
    (f₂ : P →ₗ[A] Q) (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) {x : ⋀[A]^2 P} (hx : x ∈ filtration u₁) :
    exteriorPower.map 2 f₂ x ∈ filtration u₂ := by
  obtain ⟨y, rfl⟩ := hx
  rw [← LinearMap.comp_apply, map_comp_wedgeLeft f₁ f₂ h]
  exact wedgeLeft_mem_filtration u₂ _

/-- **The map `Fil(u₁) → Fil(u₂)` induced by a commutative square** `f₂ ∘ u₁ = u₂ ∘ f₁`: the
restriction of `⋀² f₂`. -/
noncomputable def filtrationMap {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q')
    (f₂ : P →ₗ[A] Q) (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) : filtration u₁ →ₗ[A] filtration u₂ :=
  (exteriorPower.map 2 f₂).restrict fun _ hx => map_mem_filtration f₁ f₂ h hx

/-- `filtrationMap` is the restriction of `⋀² f₂`. -/
@[simp]
theorem coe_filtrationMap {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q')
    (f₂ : P →ₗ[A] Q) (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) (x : filtration u₁) :
    (filtrationMap f₁ f₂ h x : ⋀[A]^2 Q) = exteriorPower.map 2 f₂ x :=
  rfl

/-- The inclusions `Fil ⊆ ⋀²` are natural. -/
theorem subtype_comp_filtrationMap {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q')
    (f₂ : P →ₗ[A] Q) (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) :
    (filtration u₂).subtype ∘ₗ filtrationMap f₁ f₂ h =
      exteriorPower.map 2 f₂ ∘ₗ (filtration u₁).subtype :=
  rfl

/-- The identity square induces the identity of `Fil`. -/
theorem filtrationMap_id (u : P' →ₗ[A] P) :
    filtrationMap (u₁ := u) LinearMap.id LinearMap.id rfl = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext (by simp [exteriorPower.map_id])

/-- `filtrationMap` is compatible with the composition of squares. -/
theorem filtrationMap_comp {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} {u₃ : R' →ₗ[A] R}
    (f₁ : P' →ₗ[A] Q') (f₂ : P →ₗ[A] Q) (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁)
    (g₁ : Q' →ₗ[A] R') (g₂ : Q →ₗ[A] R) (h' : g₂ ∘ₗ u₂ = u₃ ∘ₗ g₁) :
    filtrationMap (g₁ ∘ₗ f₁) (g₂ ∘ₗ f₂)
        (by rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, h', LinearMap.comp_assoc]) =
      filtrationMap g₁ g₂ h' ∘ₗ filtrationMap f₁ f₂ h :=
  LinearMap.ext fun x => Subtype.ext (by simp [exteriorPower.map_comp])

/-- The maps `⋀² P' → Fil` are natural. -/
theorem filtrationMap_comp_toFiltration {u₁ : P' →ₗ[A] P} {u₂ : Q' →ₗ[A] Q} (f₁ : P' →ₗ[A] Q')
    (f₂ : P →ₗ[A] Q) (h : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) :
    filtrationMap f₁ f₂ h ∘ₗ toFiltration u₁ = toFiltration u₂ ∘ₗ exteriorPower.map 2 f₁ :=
  LinearMap.ext fun x => Subtype.ext (by
    simp only [LinearMap.comp_apply, coe_filtrationMap, coe_toFiltration]
    rw [← LinearMap.comp_apply (exteriorPower.map 2 f₂), ← exteriorPower.map_comp, h,
      exteriorPower.map_comp, LinearMap.comp_apply])

/-- The maps `Fil → P' ⊗ P''` are natural: for a morphism `(f₁, f₂, f₃)` of sequences
`P' → P → P''` to `Q' → Q → Q''`, `(f₁ ⊗ f₃) ∘ (Fil(u₁) → P' ⊗ P'') = (Fil(u₂) → Q' ⊗ Q'') ∘
filtrationMap`. -/
theorem filtrationToTensor_comp_filtrationMap {u₁ : P' →ₗ[A] P} {v₁ : P →ₗ[A] P''}
    {u₂ : Q' →ₗ[A] Q} {v₂ : Q →ₗ[A] Q''}
    (hr₁ : ∃ r : P →ₗ[A] P', r ∘ₗ u₁ = LinearMap.id) (hvu₁ : v₁ ∘ₗ u₁ = 0)
    (hr₂ : ∃ r : Q →ₗ[A] Q', r ∘ₗ u₂ = LinearMap.id) (hvu₂ : v₂ ∘ₗ u₂ = 0)
    (f₁ : P' →ₗ[A] Q') (f₂ : P →ₗ[A] Q) (f₃ : P'' →ₗ[A] Q'')
    (h₁₂ : f₂ ∘ₗ u₁ = u₂ ∘ₗ f₁) (h₂₃ : f₃ ∘ₗ v₁ = v₂ ∘ₗ f₂) :
    filtrationToTensor u₂ v₂ hr₂ hvu₂ ∘ₗ filtrationMap f₁ f₂ h₁₂ =
      TensorProduct.map f₁ f₃ ∘ₗ filtrationToTensor u₁ v₁ hr₁ hvu₁ := by
  refine filtration_hom_ext fun a b => ?_
  have e : filtrationMap f₁ f₂ h₁₂ ⟨exteriorPower.ιMulti A 2 ![u₁ a, b],
      ιMulti_mem_filtration u₁ a b⟩ =
      ⟨exteriorPower.ιMulti A 2 ![u₂ (f₁ a), f₂ b], ιMulti_mem_filtration u₂ _ _⟩ := by
    exact Subtype.ext (map_ιMulti_two f₁ f₂ h₁₂ a b)
  rw [LinearMap.comp_apply, e, filtrationToTensor_apply_ιMulti, LinearMap.comp_apply,
    filtrationToTensor_apply_ιMulti, TensorProduct.map_tmul]
  exact congrArg _ (LinearMap.congr_fun h₂₃ b).symm

end naturality

end Stacks.ExteriorSquare

/-! ### Diagrams of modules, e.g. simplicial modules -/

namespace Stacks.ExteriorSquare

open CategoryTheory Limits MonoidalCategory

universe u

variable {J : Type*} [Category* J] {A : Type u} [CommRing A]

/-- For a natural transformation `α : F ⟶ G` of diagrams of `A`-modules, the diagram
`j ↦ Fil(α j) ⊆ ⋀² (G j)`, with transition maps the restrictions of the `⋀² (G φ)`. -/
noncomputable def filtrationFunctor {F G : J ⥤ ModuleCat.{u} A} (α : F ⟶ G) :
    J ⥤ ModuleCat.{u} A where
  obj j := ModuleCat.of A (filtration (α.app j).hom)
  map {j k} φ := ModuleCat.ofHom (filtrationMap (F.map φ).hom (G.map φ).hom
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, α.naturality]))
  map_id j := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    simp [exteriorPower.map_id]))
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    simp [exteriorPower.map_comp]))

/-- The value of `filtrationFunctor α` at `j` is `Fil(α j)`. -/
@[simp]
theorem filtrationFunctor_obj {F G : J ⥤ ModuleCat.{u} A} (α : F ⟶ G) (j : J) :
    (filtrationFunctor α).obj j = ModuleCat.of A (filtration (α.app j).hom) :=
  rfl

/-- The transition maps of `filtrationFunctor α` are the maps `filtrationMap`. -/
theorem filtrationFunctor_map_hom {F G : J ⥤ ModuleCat.{u} A} (α : F ⟶ G) {j k : J}
    (φ : j ⟶ k) :
    ((filtrationFunctor α).map φ).hom = filtrationMap (F.map φ).hom (G.map φ).hom
      (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, α.naturality]) :=
  rfl

/-- A split monomorphism of modules has a linear retraction. -/
theorem exists_retraction_hom {M N : ModuleCat.{u} A} (f : M ⟶ N) (hf : IsSplitMono f) :
    ∃ r : N →ₗ[A] M, r ∘ₗ f.hom = LinearMap.id :=
  ⟨(retraction f).hom, by rw [← ModuleCat.hom_comp, IsSplitMono.id, ModuleCat.hom_id]⟩

/-- The composite of the two maps of a short complex of diagrams of modules vanishes at each
object. -/
theorem hom_g_app_comp_hom_f_app (S : ShortComplex (J ⥤ ModuleCat.{u} A)) (j : J) :
    (S.g.app j).hom ∘ₗ (S.f.app j).hom = 0 := by
  rw [← ModuleCat.hom_comp, ← NatTrans.comp_app, S.zero, NatTrans.app_zero, ModuleCat.hom_zero]

/-- **The short complex `0 → ⋀² X₁ → Fil → X₁ ⊗ X₃ → 0` of diagrams of modules** attached to a
short complex `X₁ → X₂ → X₃` of diagrams of `A`-modules which is objectwise split on the left. The
middle term is `filtrationFunctor S.f`, the first map is objectwise `toFiltration`, the second is
objectwise `filtrationToTensor`; none of them depends on a choice of splittings. -/
noncomputable def filtrationShortComplex (S : ShortComplex (J ⥤ ModuleCat.{u} A))
    (hsplit : ∀ j, IsSplitMono (S.f.app j)) : ShortComplex (J ⥤ ModuleCat.{u} A) where
  X₁ := S.X₁ ⋙ ModuleCat.exteriorPower.functor.{u, u} A 2
  X₂ := filtrationFunctor S.f
  X₃ := S.X₁ ⊗ S.X₃
  f :=
    { app j := ModuleCat.ofHom (toFiltration (S.f.app j).hom)
      naturality j k φ := ModuleCat.hom_ext
        (filtrationMap_comp_toFiltration (S.X₁.map φ).hom (S.X₂.map φ).hom
          (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, S.f.naturality])).symm }
  g :=
    { app j := ModuleCat.ofHom (filtrationToTensor (S.f.app j).hom (S.g.app j).hom
        (exists_retraction_hom _ (hsplit j)) (hom_g_app_comp_hom_f_app S j))
      naturality j k φ := ModuleCat.hom_ext
        (filtrationToTensor_comp_filtrationMap (exists_retraction_hom _ (hsplit j))
          (hom_g_app_comp_hom_f_app S j) (exists_retraction_hom _ (hsplit k))
          (hom_g_app_comp_hom_f_app S k)
          (S.X₁.map φ).hom (S.X₂.map φ).hom (S.X₃.map φ).hom
          (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, S.f.naturality])
          (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, S.g.naturality])) }
  zero := NatTrans.ext (funext fun j => ModuleCat.hom_ext
    (filtrationToTensor_comp_toFiltration (exists_retraction_hom _ (hsplit j))
      (hom_g_app_comp_hom_f_app S j)))

/-- **The short complex `0 → Fil → ⋀² X₂ → ⋀² X₃ → 0` of diagrams of modules** attached to a
short complex `X₁ → X₂ → X₃` of diagrams of `A`-modules: the inclusion of `filtrationFunctor S.f`
followed by `⋀² S.g`. -/
noncomputable def exteriorSquareShortComplex (S : ShortComplex (J ⥤ ModuleCat.{u} A)) :
    ShortComplex (J ⥤ ModuleCat.{u} A) where
  X₁ := filtrationFunctor S.f
  X₂ := S.X₂ ⋙ ModuleCat.exteriorPower.functor.{u, u} A 2
  X₃ := S.X₃ ⋙ ModuleCat.exteriorPower.functor.{u, u} A 2
  f :=
    { app j := ModuleCat.ofHom (filtration (S.f.app j).hom).subtype
      naturality _ _ _ := rfl }
  g := Functor.whiskerRight S.g (ModuleCat.exteriorPower.functor.{u, u} A 2)
  zero := NatTrans.ext (funext fun j => ModuleCat.hom_ext (LinearMap.ext
    fun (x : filtration (S.f.app j).hom) =>
      filtration_le_ker_map (hom_g_app_comp_hom_f_app S j) x.2))

variable (S : ShortComplex (J ⥤ ModuleCat.{u} A))

/-- Objectwise exactness and epimorphy of `S.g` give exactness and surjectivity of the linear
maps. -/
private theorem exact_surjective_hom
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat.{u} A)).obj j)).Exact)
    (hg : ∀ j, Epi (S.g.app j)) (j : J) :
    Function.Exact (S.f.app j).hom (S.g.app j).hom ∧ Function.Surjective (S.g.app j).hom :=
  ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS j),
    (ModuleCat.epi_iff_surjective _).mp (hg j)⟩

/-- At each object, `0 → ⋀² X₁ → Fil → X₁ ⊗ X₃ → 0` is short exact, provided `X₁ → X₂ → X₃` is
there exact, with `X₂ → X₃` surjective and `X₁ → X₂` split injective. -/
theorem filtrationShortComplex_shortExact_app
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat.{u} A)).obj j)).Exact)
    (hg : ∀ j, Epi (S.g.app j)) (hsplit : ∀ j, IsSplitMono (S.f.app j)) (j : J) :
    ((filtrationShortComplex S hsplit).map
      ((evaluation J (ModuleCat.{u} A)).obj j)).ShortExact := by
  obtain ⟨hex, hsurj⟩ := exact_surjective_hom S hS hg j
  have hr := exists_retraction_hom _ (hsplit j)
  have hvu := hom_g_app_comp_hom_f_app S j
  exact
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        (exact_toFiltration_filtrationToTensor hr hvu hex hsurj)
      mono_f := (ModuleCat.mono_iff_injective _).mpr (toFiltration_injective hr)
      epi_g := (ModuleCat.epi_iff_surjective _).mpr
        (filtrationToTensor_surjective hr hvu hsurj) }

/-- At each object, `0 → Fil → ⋀² X₂ → ⋀² X₃ → 0` is short exact, provided `X₁ → X₂ → X₃` is
there exact with `X₂ → X₃` surjective; no splitting is needed. -/
theorem exteriorSquareShortComplex_shortExact_app
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat.{u} A)).obj j)).Exact)
    (hg : ∀ j, Epi (S.g.app j)) (j : J) :
    ((exteriorSquareShortComplex S).map ((evaluation J (ModuleCat.{u} A)).obj j)).ShortExact := by
  obtain ⟨hex, hsurj⟩ := exact_surjective_hom S hS hg j
  exact
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        (exact_subtype_map hex hsurj)
      mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (exteriorPower.map_surjective hsurj) }

/-- A short complex of diagrams of modules which is short exact at every object is short
exact. -/
private theorem shortExact_of_evaluation {T : ShortComplex (J ⥤ ModuleCat.{u} A)}
    (h : ∀ j, (T.map ((evaluation J (ModuleCat.{u} A)).obj j)).ShortExact) : T.ShortExact where
  exact := by
    rw [T.exact_iff_isZero_homology]
    exact Functor.isZero _ fun j =>
      ((T.map ((evaluation J _).obj j)).exact_iff_isZero_homology.mp (h j).exact).of_iso
        (T.mapHomologyIso ((evaluation J _).obj j)).symm
  mono_f := (NatTrans.mono_iff_mono_app _).mpr fun j => (h j).mono_f
  epi_g := (NatTrans.epi_iff_epi_app _).mpr fun j => (h j).epi_g

/-- **`0 → ⋀² X₁ → Fil → X₁ ⊗ X₃ → 0` is a short exact sequence of diagrams of modules** for a
short complex `X₁ → X₂ → X₃` of diagrams of `A`-modules which is objectwise exact, objectwise
surjective on the right and objectwise split injective on the left. The splittings need not be
compatible with the transition maps. -/
@[sga "6 V 2.2.1" "special case"]
theorem filtrationShortComplex_shortExact
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat.{u} A)).obj j)).Exact)
    (hg : ∀ j, Epi (S.g.app j)) (hsplit : ∀ j, IsSplitMono (S.f.app j)) :
    (filtrationShortComplex S hsplit).ShortExact :=
  shortExact_of_evaluation (filtrationShortComplex_shortExact_app S hS hg hsplit)

/-- **`0 → Fil → ⋀² X₂ → ⋀² X₃ → 0` is a short exact sequence of diagrams of modules** for a
short complex `X₁ → X₂ → X₃` of diagrams of `A`-modules which is objectwise exact and objectwise
surjective on the right. -/
@[sga "6 V 2.2.1" "special case"]
theorem exteriorSquareShortComplex_shortExact
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat.{u} A)).obj j)).Exact)
    (hg : ∀ j, Epi (S.g.app j)) :
    (exteriorSquareShortComplex S).ShortExact :=
  shortExact_of_evaluation (exteriorSquareShortComplex_shortExact_app S hS hg)

end Stacks.ExteriorSquare
