module

public import Mathlib.FieldTheory.Galois.Profinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeTwoCocycles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.FourTermVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.HighDegreeFromBoundedTorsion
import StacksCore.Tactic.StacksAttribute

/-!
# Galois cohomology of the units of a Galois extension

Let `K` be a field and let `Ω/K` be a Galois extension. This file shows that the continuous group
cohomology `H^q(Gal(Ω/K), Ωˣ)` vanishes in degree one, in degree two when `Br(K) = 0`, and in
every degree `q ≥ 1` when moreover suitable torsion modules have vanishing cohomology in degrees
`q ≥ 2`.

## Main results

* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_one`:
  `H¹(Gal(Ω/K), Ωˣ) = 0`.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_two`: if `Br(K) = 0` then
  `H²(Gal(Ω/K), Ωˣ) = 0`.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_of_fourTerm`: if `Br(K) = 0`
  and `Ωˣ` sits in a four-term exact sequence `0 → A → Ωˣ → V → B → 0` with `V` a `ℚ`-vector
  space and `A`, `B` without cohomology in degrees `q ≥ 2`, then `H^q(Gal(Ω/K), Ωˣ) = 0` for
  every `q ≥ 1`.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_of_annihilated`: if `Br(K) = 0`
  and every discrete module annihilated by a nonzero integer has vanishing cohomology in degrees
  `q ≥ 2`, then `H^q(Gal(Ω/K), Ωˣ) = 0` for every `q ≥ 1`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IntermediateField groupCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.GaloisCohomology

/-- `ℤ`-modules are regarded as topological spaces with the discrete topology. -/
local instance : HasForget₂ (ModuleCat.{u} ℤ) TopCat.{u} :=
  { forget₂ := forget (ModuleCat.{u} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The Galois group of a Galois extension is profinite in the sense of
`Stacks.Chapter05.Tag_0BR1.IsProfiniteTop`: compact, Hausdorff and totally disconnected for the
Krull topology. -/
theorem isProfiniteTop_galoisGroup :
    Stacks.Chapter05.Tag_0BR1.IsProfiniteTop Gal(Ω/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The Galois action on `Stacks.GaloisCohomology.unitsContinuousGModule` is the action on the
units, written additively. -/
@[simp] theorem unitsContinuousGModule_ρ_hom (g : Gal(Ω/K)) (a : Additive Ωˣ) :
    (((unitsContinuousGModule K Ω).obj.obj.ρ g).hom a : Additive Ωˣ) =
      Additive.ofMul (g • a.toMul) := rfl

/-- **Hilbert's theorem 90 for an infinite Galois extension, written additively.** Every locally
constant `1`-cocycle of `Gal(Ω/K)` with values in `Additive Ωˣ` is a coboundary. -/
@[sga "4½ Arcata 1.5.3" "more general"]
theorem exists_sub_eq_of_isCocycle_additive_units (c : Gal(Ω/K) → Additive Ωˣ)
    (hloc : IsLocallyConstant c)
    (hcoc : ∀ g₁ g₂ : Gal(Ω/K), c (g₁ * g₂) = Additive.ofMul (g₁ • (c g₂).toMul) + c g₁) :
    ∃ x : Additive Ωˣ, ∀ g : Gal(Ω/K), Additive.ofMul (g • x.toMul) - x = c g := by
  have hfloc : IsLocallyConstant fun g : Gal(Ω/K) ↦ (c g).toMul :=
    hloc.comp Additive.toMul
  have hfcoc : IsMulCocycle₁ fun g : Gal(Ω/K) ↦ (c g).toMul := fun g h ↦ by
    simpa using congrArg (fun z : Additive Ωˣ ↦ z.toMul) (hcoc g h)
  obtain ⟨xu, hxu⟩ := isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ _ hfloc hfcoc
  refine ⟨Additive.ofMul xu, fun g ↦ ?_⟩
  simpa using congrArg (fun z : Ωˣ ↦ Additive.ofMul z) (hxu g)

/-- If `Br(K) = 0`, then every locally constant `2`-cocycle of `Gal(Ω/K)` with values in
`Additive Ωˣ` is the coboundary of a locally constant `1`-cochain. -/
theorem exists_isLocallyConstant_sub_eq_of_isCocycle₂_additive_units
    (hBr : ∀ y : BrauerGroup K, y = 1) (d : Gal(Ω/K) × Gal(Ω/K) → Additive Ωˣ)
    (hdloc : IsLocallyConstant d)
    (hdcoc : ∀ g₁ g₂ g₃ : Gal(Ω/K), d (g₁ * g₂, g₃) + d (g₁, g₂) =
      Additive.ofMul (g₁ • (d (g₂, g₃)).toMul) + d (g₁, g₂ * g₃)) :
    ∃ x : Gal(Ω/K) → Additive Ωˣ, IsLocallyConstant x ∧
      ∀ g₁ g₂ : Gal(Ω/K),
        Additive.ofMul (g₁ • (x g₂).toMul) - x (g₁ * g₂) + x g₁ = d (g₁, g₂) := by
  obtain ⟨f, rfl⟩ : ∃ f : Gal(Ω/K) × Gal(Ω/K) → Ωˣ, d = fun p ↦ Additive.ofMul (f p) :=
    ⟨fun p ↦ Additive.toMul (d p), funext fun _ ↦ rfl⟩
  have hfloc : IsLocallyConstant f := hdloc.comp Additive.toMul
  have hfcoc : IsMulCocycle₂ f := by
    intro g h j
    have h1 := congrArg (fun z : Additive Ωˣ ↦ z.toMul) (hdcoc g h j)
    simp only [toMul_add, toMul_ofMul] at h1
    exact h1
  obtain ⟨x, hxloc, hx⟩ :=
    exists_isLocallyConstant_isMulCoboundary₂_of_forall_finiteGalois
      (fun _ F hF ↦ isMulCoboundary₂_of_brauer (fun y _ ↦ hBr y) F hF) f hfloc hfcoc
  refine ⟨fun g ↦ Additive.ofMul (x g), hxloc.comp Additive.ofMul,
    fun g₁ g₂ ↦ ?_⟩
  have h2 := congrArg (fun u : Ωˣ ↦ Additive.ofMul u) (hx g₁ g₂)
  simp only [ofMul_mul, ofMul_div, toMul_ofMul] at h2 ⊢
  exact h2

/-- For a Galois extension `Ω/K`, the continuous group cohomology `H¹(Gal(Ω/K), Ωˣ)` of the
discrete Galois module `Stacks.GaloisCohomology.unitsContinuousGModule` vanishes. -/
@[stacks 03R8 "part (1) at q = 1, for the derived-functor groups H^q(Gal(Ω/K), Ωˣ) of
Stacks 04JR, with NO HYPOTHESIS WHATSOEVER -- STRONGER than the proposition at q = 1 in two
independent ways. First, the proposition assumes Br(K') = 0 uniformly over every finite extension
K'/K and this assumes nothing about Brauer groups at all: the cocycle statement at q = 1 is
Hilbert 90 for an infinite Galois extension, namely
isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁, which is unconditional, so the
proposition's hypothesis is not used and is not needed. Second, Ω is an arbitrary Galois extension
rather than the separable closure; at Ω = K^sep this is exactly the tag's q = 1 case. Nothing is
carried: the comparison between the cocycle and derived-functor descriptions is
Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary, which
is a theorem, not a hypothesis. NOT proved here: the degrees q ≥ 2 of
part (1) -- q = 2 is isZero_continuousGroupCohomology_units_two just below, over the tag's own
hypothesis in the weaker form Br(K) = 0, and the degrees q ≥ 3 are
isZero_continuousGroupCohomology_units_of_fourTerm and
isZero_continuousGroupCohomology_units_of_annihilated, which still carry part (2) -- and
part (2) itself", sga "4½ Arcata 1.5.3" "more general"]
theorem isZero_continuousGroupCohomology_units_one :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) 1 (unitsContinuousGModule K Ω)) :=
  Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary
    (unitsContinuousGModule K Ω) (exists_sub_eq_of_isCocycle_additive_units K Ω)

/-- Let `K` be a field with `Br(K) = 0` and let `Ω/K` be a Galois extension. Then the continuous
group cohomology `H²(Gal(Ω/K), Ωˣ)` of the discrete Galois module
`Stacks.GaloisCohomology.unitsContinuousGModule` vanishes. -/
@[stacks 03R8 "part (1) at q = 2, for the derived-functor groups H^q(Gal(Ω/K), Ωˣ) of
Stacks 04JR. Nothing is carried: no comparison between the cocycle and derived-functor
descriptions is assumed, and the only hypothesis is Br(K) = 0. That is STRICTLY WEAKER than the
proposition's own hypothesis, which assumes Br(K') = 0 uniformly over every finite extension
K'/K -- Br(K) = 0 is one instance of it, and it already forces every relative Brauer group
Br(L/K) to vanish, which is what the crossed-product argument needs at each finite Galois
subextension. Ω is an arbitrary Galois extension rather than the separable closure, so this is
more general than the tag's degree-two case in that respect too; at Ω = K^sep it is exactly that
case. The cocycle input is isMulCoboundary₂_of_brauer, assembled by
exists_isLocallyConstant_isMulCoboundary₂_of_forall_finiteGalois (which records that the
trivialising 1-cochain, being inflated from a finite level, is locally constant -- strictly more
than Mathlib's IsMulCoboundary₂ gives, and exactly what the comparison consumes); the comparison
itself is Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_forall_isCoboundary, which
is a theorem, not a hypothesis. NOT proved here: q = 1 of
part (1), which is isZero_continuousGroupCohomology_units_one above and needs no Brauer
hypothesis at all; the degrees q >= 3, which are
isZero_continuousGroupCohomology_units_of_fourTerm and
isZero_continuousGroupCohomology_units_of_annihilated and still carry part (2); and part (2)
itself",
  sga "4½ Arcata 3.1.6" "clause i), degree q=2"]
theorem isZero_continuousGroupCohomology_units_two (hBr : ∀ y : BrauerGroup K, y = 1) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) 2 (unitsContinuousGModule K Ω)) :=
  Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_forall_isCoboundary
    (unitsContinuousGModule K Ω)
    (exists_isLocallyConstant_sub_eq_of_isCocycle₂_additive_units K Ω hBr)

/-- If `Br(K) = 0`, vanishing of `H^q(Gal(Ω/K), Ωˣ)` for `q ≥ 3` gives it for all `q ≥ 1`. -/
private theorem isZero_units_of_three_le (hBr : ∀ y : BrauerGroup K, y = 1) (q : ℕ) (hq : 1 ≤ q)
    (h : 3 ≤ q →
      IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω))) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)) := by
  match q, hq with
  | 1, _ => exact isZero_continuousGroupCohomology_units_one K Ω
  | 2, _ => exact isZero_continuousGroupCohomology_units_two K Ω hBr
  | _ + 3, _ => exact h (by lia)

/-- Let `K` be a field with `Br(K) = 0` and let `Ω/K` be a Galois extension. Let `S₁` and `S₂`
be short exact sequences of discrete `Gal(Ω/K)`-modules with `S₁.X₂ ≅ Ωˣ` and `S₁.X₃ ≅ S₂.X₁`,
so that they splice to a four-term exact sequence `0 → S₁.X₁ → Ωˣ → S₂.X₂ → S₂.X₃ → 0`. If
`S₂.X₂` is a `ℚ`-vector space and `S₁.X₁` and `S₂.X₃` have vanishing cohomology in degrees
`q ≥ 2`, then `H^q(Gal(Ω/K), Ωˣ) = 0` for every `q ≥ 1`. -/
theorem isZero_continuousGroupCohomology_units_of_fourTerm (hBr : ∀ y : BrauerGroup K, y = 1)
    (S₁ S₂ : ShortComplex (ContinuousGModule.{u, u} Gal(Ω/K)))
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (hmid : S₁.X₂ ≅ unitsContinuousGModule K Ω) (e : S₁.X₃ ≅ S₂.X₁)
    (hrat : Module ℚ S₂.X₂.1.1.V)
    (h03R8₂sub : ∀ q : ℕ, 2 ≤ q →
      IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q S₁.X₁))
    (h03R8₂quot : ∀ q : ℕ, 2 ≤ q →
      IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q S₂.X₃))
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)) := by
  refine isZero_units_of_three_le K Ω hBr q hq fun h3 ↦ ?_
  let := hrat
  refine (Iso.isZero_iff
    ((continuousGroupCohomologyFunctor.{u, u} Gal(Ω/K) q).mapIso hmid)).1 ?_
  exact Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_fourTerm_rat.{u, u}
    (isProfiniteTop_galoisGroup K Ω) hS₁ hS₂ e h03R8₂sub h03R8₂quot q (by lia)

/-- Let `K` be a field with `Br(K) = 0` and let `Ω/K` be a Galois extension. If
`H^q(Gal(Ω/K), N) = 0` for every `q ≥ 2` and every discrete `Gal(Ω/K)`-module `N` annihilated by
a nonzero integer, then `H^q(Gal(Ω/K), Ωˣ) = 0` for every `q ≥ 1`. -/
theorem isZero_continuousGroupCohomology_units_of_annihilated (hBr : ∀ y : BrauerGroup K, y = 1)
    (h03R8₂ : ∀ (N : ContinuousGModule.{u, u} Gal(Ω/K)) (m : ℤ), m ≠ 0 → m • 𝟙 N = 0 →
      ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q N))
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)) := by
  refine isZero_units_of_three_le K Ω hBr q hq fun h3 ↦ ?_
  exact Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_three_le_of_annihilated.{u, u}
    Gal(Ω/K) (isProfiniteTop_galoisGroup K Ω) h03R8₂ (unitsContinuousGModule K Ω) q (by lia)

end Stacks.GaloisCohomology

end
