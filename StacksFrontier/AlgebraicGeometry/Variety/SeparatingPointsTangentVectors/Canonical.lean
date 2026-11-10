module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoComplete

/-!
# A linear system separating points and tangent vectors, at the canonical morphism

Let `k` be an algebraically closed field, let `X` be a proper `k`-scheme, let `ℒ` be an
invertible `𝒪_X`-module and let `V ⊂ H⁰(X, ℒ)` be a `k`-subvector space such that

1. for every pair of distinct closed points `x, y ∈ X` some `s ∈ V` vanishes at `x` but not at
   `y`, and
2. for every closed point `x ∈ X` and every nonzero tangent vector `θ ∈ T_{X/k, x}` some
   `s ∈ V` vanishes at `x` but has nonzero pullback by `θ`.

Then `ℒ` is very ample and the canonical morphism `φ_{ℒ,V} : X ⟶ 𝐏(V)` is a closed immersion.
This file proves that, with no assumed data: neither the morphism to projective space nor the
identification of the pulled-back twist nor finite-dimensionality of `V` is a hypothesis below.

## Main results

* `isRelativelyVeryAmple_and_isClosedImmersion_toProjectiveSpaceOfModule_of_separates`:
  **[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)**, under the source's
  hypotheses and with nothing assumed.
* `AlgebraicGeometry.generatesStalks_id_of_separatesClosedPoints`: separation of closed points
  makes the *complete* linear system `H⁰(X, ℒ)` generate `ℒ`.
* `AlgebraicGeometry.generatesStalks_of_separatesClosedPoints`: separation of closed points makes
  `V` itself generate `ℒ`, on a scheme no closed point of which is its only one.
* `AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver`: **the
  identification `φ_{(ℒ, (s₀, …, sₙ))}^* 𝒪(1) ≅ ℒ` at the canonical morphism of
  [Stacks, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)**, carrying the pullback of the
  `i`-th homogeneous coordinate to `sᵢ`.

## How the four conclusions are reached

**Finite-dimensionality of `V`** is `AlgebraicGeometry.moduleFinite_sections_of_isProper`, which
is [Stacks, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6) for an invertible module on a
proper scheme over a field, together with the fact that a subspace of a finite-dimensional space
is finite-dimensional. Nothing below assumes it.

**Very ampleness** is reached through the *complete* system. Separation of closed points makes
`H⁰(X, ℒ)` generate `ℒ` — at a closed point `x` with a second closed point `y` beside it,
condition (1) applied to the ordered pair `(y, x)` produces a section not vanishing at `x`, and
on a one-point scheme an invertible module has a nonvanishing global section outright
(`AlgebraicGeometry.exists_mem_nonvanishingLocus_of_subsingleton`). A basis of the
finite-dimensional space `H⁰(X, ℒ)`, padded with the zero section, is then a finite generating
family; the morphism `φ : X ⟶ ℙⁿ_k` it defines carries `𝒪(1)` to `ℒ`, every global section of
`ℒ` is in the image of the comparison because the basis spans, and conditions (1) and (2) make
`φ` a closed immersion. Projective space over `Spec k` is the projective bundle of a free
module, which turns that immersion into the datum relative very ampleness asks for.

**The canonical morphism `φ_{ℒ,V} : X ⟶ 𝐏(V)`** is
`AlgebraicGeometry.toProjectiveSpaceOfModule`, the morphism of
[Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY) read in a basis of `V`: the
morphism `φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ ℙⁿ_k` of the images of the basis, composed with the
coordinate isomorphism `ℙⁿ_k ≅ 𝐏(V)` of the basis. The conclusion is stated for *every* basis of
`V`, which is how the source's basis-free `φ_{ℒ,V}` is expressed here. That it is a closed
immersion uses the twist identification at the canonical morphism together with the fact that the
basis spans `V`, so that every member of `V` — in particular each separating section conditions
(1) and (2) produce — is in the image of the comparison.

**Generation of `ℒ` by `V`**, which is what makes `φ_{ℒ,V}` exist at all, is the one conclusion
carrying a side condition, and the side condition is exactly the gap in the source's proof
discussed next.

## The one-closed-point gap in the source

The source's proof opens with "condition (1) implies in particular that the elements of `V`
generate `ℒ` over `X`". That implication needs a *second* closed point: condition (1) applied to
an ordered pair `(y, x)` of distinct closed points is what produces a section of `V` not
vanishing at `x`. On a scheme with exactly one closed point both conditions can hold while `V`
generates nothing, and then `φ_{ℒ,V}` does not exist; the module documentation of
`StacksFrontier/AlgebraicGeometry/Variety/SeparatingPointsTangentVectors/Basic.lean` records two
witnesses, both proper over `k`, namely `X = Spec k` with `ℒ = 𝒪_X` and `V = 0`, and
`X = Spec (k[t]/t²)` with `ℒ = 𝒪_X` and `V = k · t`.

Nothing is assumed about `X` on that account. Generation of `ℒ` by `V` appears in the conclusion
guarded by its precise side condition — no closed point of `X` is the only one, which is vacuous
on the empty scheme and fails only in the one-point case — and the closed-immersion clause is
stated for each basis of `V` whose family of images generates `ℒ`, which is precisely the datum
`φ_{ℒ,V}` is built from. Very ampleness, finite-dimensionality of `V`, and the closed-immersion
clause carry no side condition at all.

## References

* [Stacks Project, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample (IsInvertibleModule)
open Stacks.ProjectiveFromSections
open Stacks.AmpleProjectiveImmersion (twistingSheafAtUniverse projectiveSpaceTwistingSheaf)
open Stacks.TwistPullbackPinned (coordGlobalSection pullbackCoordSection)

universe u

namespace AlgebraicGeometry

/-! ### Generation from nonvanishing at the closed points -/

/-- **A family of global sections of an invertible module with a nonvanishing member at every
closed point generates the stalks.** The points at which every member vanishes form a closed set
meeting no closed point, and the closed points are dense in every closed subset of a scheme
locally of finite type over a field. -/
theorem generatesStalks_of_forall_isClosed_exists_mem_nonvanishingLocus {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (L : X.Modules)
    [IsInvertibleModule X L] {ι : Type u} (t : ι → Γ(L, ⊤))
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Stacks.Ample.nonvanishingLocus L (t i)) :
    GeneratesStalks t := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine generatesStalks_of_forall_exists_mem_nonvanishingLocus L t fun z => ?_
  by_contra hz
  push Not at hz
  set Z : Set X := {w : X | ∀ i, w ∉ Stacks.Ample.nonvanishingLocus L (t i)} with hZ
  have hZclosed : IsClosed Z := by
    rw [hZ, show {w : X | ∀ i, w ∉ Stacks.Ample.nonvanishingLocus L (t i)} =
      (⋃ i, Stacks.Ample.nonvanishingLocus L (t i))ᶜ by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]]
    exact isClosed_compl_iff.mpr (isOpen_iUnion fun i =>
      Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X L (t i))
  have hempty : Z ∩ closedPoints X = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    obtain ⟨i, hi⟩ := h w hw.2
    exact hw.1 i hi
  have hclosure := JacobsonSpace.closure_inter_closedPoints hZclosed
  rw [hempty, closure_empty] at hclosure
  exact (hclosure ▸ hz : z ∈ (∅ : Set X))

/-- **A section nonvanishing at a point forces a member of any family spanning it to be
nonvanishing there.** The sections whose germ at the point lies in `𝔪ₓ · ℒₓ` form a
`k`-submodule, the germ map being semilinear and the base field acting through `Γ(X, 𝒪_X)`. -/
theorem exists_mem_nonvanishingLocus_of_mem_span {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : X.Modules) [IsInvertibleModule X L] {ι : Type*}
    (t : ι → Γ(L, ⊤)) {z : X} {σ : Γ(L, ⊤)}
    (hz : z ∈ Stacks.Ample.nonvanishingLocus L σ) :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    σ ∈ Submodule.span k (Set.range t) →
      ∃ i, z ∈ Stacks.Ample.nonvanishingLocus L (t i) := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  intro hσ
  by_contra hno
  push Not at hno
  have hvanish : ∀ i, (L.presheaf.Γgerm z).hom (t i) ∈ Stacks.ModuleStalk.maximalSmul L z := by
    intro i
    have := hno i
    rwa [Stacks.Ample.mem_nonvanishingLocus_iff, not_not] at this
  have hsub : ∀ τ ∈ Submodule.span k (Set.range t),
      (L.presheaf.Γgerm z).hom τ ∈ Stacks.ModuleStalk.maximalSmul L z := by
    intro τ hτ
    induction hτ using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hvanish i
    | zero => simp
    | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [show (c • a : Γ(L, ⊤)) = baseRingMap p c • a from rfl, Stacks.ModuleStalk.Γgerm_smul]
      exact Submodule.smul_mem _ _ ha
  rw [Stacks.Ample.mem_nonvanishingLocus_iff] at hz
  exact hz (hsub σ hσ)

/-- **A finite family whose span contains a generating system generates.** At every point a
member of the generating system is nonvanishing, hence so is a member of the family. -/
theorem generatesStalks_fin_of_mem_span {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : X.Modules) [IsInvertibleModule X L] {m : ℕ}
    (t : Fin m → Γ(L, ⊤)) {ι : Type u} (ψ : ι → Γ(L, ⊤)) (hgen : GeneratesStalks ψ) :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    (∀ i, ψ i ∈ Submodule.span k (Set.range t)) → GeneratesStalks t := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  intro hspan
  rw [← generatesStalks_ulift_iff]
  refine generatesStalks_of_forall_exists_mem_nonvanishingLocus L _ fun z => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks ψ hgen z
  obtain ⟨j, hj⟩ := exists_mem_nonvanishingLocus_of_mem_span p L t hi (hspan i)
  exact ⟨ULift.up j, hj⟩

/-- A member of a submodule lies in the span of the images of any basis of that submodule. -/
theorem mem_span_range_coe_basis {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (V : Submodule R M) {ι : Type*} (b : Module.Basis ι R V) (v : V) :
    (v : M) ∈ Submodule.span R (Set.range fun i => ((b i : V) : M)) := by
  have h1 : v ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := V.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

/-! ### What condition (1) gives at a closed point -/

/-- **Condition (1) produces a section of the system not vanishing at a closed point**, provided
a second closed point is available: the ordered pair `(y, x)` gives a member of the family
vanishing at `y` and not at `x`, and a section not vanishing at a point is nonvanishing
there. -/
theorem exists_mem_nonvanishingLocus_of_separatesClosedPoints {X : Scheme.{u}} {L : X.Modules}
    {ι : Type u} {ψ : ι → Γ(L, ⊤)} (hpoints : SeparatesClosedPoints ψ) (x y : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) (hyx : y ≠ x) :
    ∃ i, x ∈ Stacks.Ample.nonvanishingLocus L (ψ i) := by
  obtain ⟨i, -, hni⟩ := hpoints y x hy hx hyx
  exact ⟨i, mem_nonvanishingLocus_of_not_vanishesAlong L x (ψ i) hni⟩

/-- **Separation of closed points makes the system itself generate `ℒ`**, on a scheme no closed
point of which is its only one.

The side condition cannot be dropped: see the section "The one-closed-point gap in the source" of
this module. It is vacuous on the empty scheme. -/
theorem generatesStalks_of_separatesClosedPoints {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (L : X.Modules) [IsInvertibleModule X L]
    {ι : Type u} {ψ : ι → Γ(L, ⊤)} (hpoints : SeparatesClosedPoints ψ)
    (hX : ∀ x : X, IsClosed ({x} : Set X) → ∃ y : X, IsClosed ({y} : Set X) ∧ y ≠ x) :
    GeneratesStalks ψ :=
  generatesStalks_of_forall_isClosed_exists_mem_nonvanishingLocus p L ψ fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hX x hx
    exact exists_mem_nonvanishingLocus_of_separatesClosedPoints hpoints x y hx hy hyx

/-- **At every closed point some global section of `ℒ` is nonvanishing**, separation of closed
points holding. With a second closed point beside `x` this is condition (1); and if there is
none, `X` is a single point and an invertible module there has a nonvanishing global section
outright. -/
theorem exists_mem_nonvanishingLocus_of_isClosed_of_separatesClosedPoints {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (L : X.Modules)
    [IsInvertibleModule X L] {ι : Type u} {ψ : ι → Γ(L, ⊤)}
    (hpoints : SeparatesClosedPoints ψ) (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ s : Γ(L, ⊤), x ∈ Stacks.Ample.nonvanishingLocus L s := by
  by_cases hsub : Subsingleton X
  · exact exists_mem_nonvanishingLocus_of_subsingleton L x
  · let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    obtain ⟨y, hy, hyx⟩ := exists_isClosed_singleton_ne hsub x hx
    obtain ⟨i, hi⟩ := exists_mem_nonvanishingLocus_of_separatesClosedPoints hpoints x y hx hy hyx
    exact ⟨ψ i, hi⟩

/-- **Separation of closed points makes the complete linear system generate `ℒ`.** Unlike
`AlgebraicGeometry.generatesStalks_of_separatesClosedPoints` this needs no hypothesis on `X`: in
the one-point case the nonvanishing section is supplied by invertibility rather than by
condition (1). -/
theorem generatesStalks_id_of_separatesClosedPoints {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (L : X.Modules) [IsInvertibleModule X L]
    {ι : Type u} {ψ : ι → Γ(L, ⊤)} (hpoints : SeparatesClosedPoints ψ) :
    GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤)) :=
  generatesStalks_of_forall_isClosed_exists_mem_nonvanishingLocus p L id fun x hx =>
    exists_mem_nonvanishingLocus_of_isClosed_of_separatesClosedPoints p L hpoints x hx

/-! ### Transporting the separation conditions along the range -/

/-- Separation of closed points by a family is inherited by any family whose range contains
its own. -/
theorem SeparatesClosedPoints.mono {X : Scheme.{u}} {L : X.Modules} {ι ι' : Type u}
    {ψ : ι → Γ(L, ⊤)} {ψ' : ι' → Γ(L, ⊤)} (h : SeparatesClosedPoints ψ)
    (hr : ∀ i, ∃ i', ψ' i' = ψ i) : SeparatesClosedPoints ψ' := fun x y hx hy hxy => by
  obtain ⟨i, h₁, h₂⟩ := h x y hx hy hxy
  obtain ⟨i', hi'⟩ := hr i
  exact ⟨i', hi' ▸ h₁, hi' ▸ h₂⟩

/-- Separation of tangent vectors by a family is inherited by any family whose range contains
its own. -/
theorem SeparatesTangentVectors.mono {X S : Scheme.{u}} {L : X.Modules} (p : X ⟶ S)
    {ι ι' : Type u} {ψ : ι → Γ(L, ⊤)} {ψ' : ι' → Γ(L, ⊤)} (h : SeparatesTangentVectors p ψ)
    (hr : ∀ i, ∃ i', ψ' i' = ψ i) : SeparatesTangentVectors p ψ' := fun x hx θ hθ => by
  obtain ⟨i, h₁, h₂⟩ := h x hx θ hθ
  obtain ⟨i', hi'⟩ := hr i
  exact ⟨i', hi' ▸ h₁, hi' ▸ h₂⟩

/-! ### A finite basis of the complete system -/

/-- **A basis of `H⁰(X, ℒ)`, padded with the zero section, generates `ℒ` and spans
`H⁰(X, ℒ)`.** The space is finite-dimensional by [Stacks, Tag 02O6], and a spanning family
generates as soon as the complete system does. -/
theorem exists_fin_basis_generatesStalks_of_generatesStalks_id {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules)
    [IsInvertibleModule X L] (hgen : GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤))) :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    ∃ (n : ℕ) (t : Fin (n + 1) → Γ(L, ⊤)),
      GeneratesStalks t ∧ ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range t) := by
  classical
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  have : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper p L
  let b := Module.finBasis k Γ(L, ⊤)
  have hspan : ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range (Fin.lastCases 0 fun j => b j :
      Fin (Module.finrank k Γ(L, ⊤) + 1) → Γ(L, ⊤))) := fun σ => by
    refine Submodule.span_mono ?_ (b.mem_span σ)
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castSucc j, by simp⟩
  exact ⟨_, _, generatesStalks_fin_of_mem_span p L _ id hgen hspan, hspan⟩

/-! ### Completeness of the realized system on a subspace -/

/-- **Every member of the span of the realized family is itself realized.** Pulling back along
`φ` and transporting along `θ` is additive and carries the action of `k` upstairs to its action
downstairs, so its image is a `k`-submodule. -/
theorem exists_eq_pullbackSectionTop_of_mem_span {k : Type u} [Field k] {X P : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : P ⟶ Spec (.of k)) (φ : X ⟶ P) (hφ : φ ≫ q = p)
    (M : P.Modules) {L : X.Modules} (θ : (Scheme.Modules.pullback φ).obj M ≅ L)
    {ι : Type*} (T : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤))
    (hpin : ∀ i, θ.hom.app ⊤ (pullbackSectionTop φ M (T i)) = t i) :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    ∀ σ ∈ Submodule.span k (Set.range t),
      ∃ u : Γ(M, ⊤), θ.hom.app ⊤ (pullbackSectionTop φ M u) = σ := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  let : Module k Γ(M, ⊤) := Module.compHom _ (baseRingMap q)
  have hΦsmul : ∀ (c : k) (u : Γ(M, ⊤)),
      θ.hom.app ⊤ (pullbackSectionTop φ M (c • u)) =
        c • θ.hom.app ⊤ (pullbackSectionTop φ M u) := by
    intro c u
    rw [show (c • u : Γ(M, ⊤)) = baseRingMap q c • u from rfl, pullbackSectionTop_smul,
      Scheme.Modules.Hom.app_smul, baseRingMap_comp p q φ hφ]
    rfl
  intro σ hσ
  induction hσ using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨T i, hpin i⟩
  | zero =>
    exact ⟨0, (congrArg (θ.hom.app ⊤) (pullbackSectionTop_zero φ M)).trans
      (θ.hom.app ⊤).hom.map_zero⟩
  | add a b _ _ ha hb =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := And.intro ha hb
    exact ⟨u + v, ((congrArg (θ.hom.app ⊤) (pullbackSectionTop_add φ M u v)).trans
      ((θ.hom.app ⊤).hom.map_add _ _)).trans (by rw [hu, hv])⟩
  | smul c a _ ha =>
    obtain ⟨u, hu⟩ := ha
    exact ⟨c • u, by rw [hΦsmul c u, hu]⟩

/-! ### The twist identification at the canonical morphism -/

/-- **The pinned twist comparison of [Stacks, Tag 01NE] at the canonical morphism
`φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ ℙⁿ_ℤ`.** The glued morphism of a generating family restricts on each
nonvanishing open to the morphism of the ratio family, which is exactly the pinning the
comparison asks for. -/
theorem exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse {X : Scheme.{u}} {n : ℕ}
    {L : X.Modules} [IsInvertibleModule X L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) :
    ∃ α : (Scheme.Modules.pullback (toProjectiveSpaceAtUniverse s hs)).obj
        (twistingSheafAtUniverse.{u} n) ⟶ L,
      IsIso α ∧ ∀ i, α.app ⊤ (pullbackCoordSection (toProjectiveSpaceAtUniverse s hs) i) = s i :=
  Stacks.TwistPullbackPinned.exists_iso_pullback_twistingSheafAtUniverse s
    (toProjectiveSpaceAtUniverse s hs) (isOpenCover_nvCover_of_generatesStalks s hs)
    (ι_toProjectiveSpaceAtUniverse s hs)

/-- **`φ_{(ℒ, (s₀, …, sₙ))}^* 𝒪(1) ≅ ℒ` at the canonical morphism to `ℙⁿ_S`**, carrying the
pullback of the `i`-th homogeneous coordinate to `sᵢ`.

The comparison of the previous statement is taken along the morphism to the integral model
underlying `φ`; the canonical isomorphism `φ^* q^* ≅ (φ ≫ q)^*` of pullback functors moves it to
a pullback along `φ` of the hyperplane sheaf of `ℙⁿ_S` itself. -/
theorem exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver {X S : Scheme.{u}} {n : ℕ}
    {L : X.Modules} [IsInvertibleModule X L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) (f : X ⟶ S) :
    ∃ θ : (Scheme.Modules.pullback (toProjectiveSpaceOver s hs f)).obj
        (projectiveSpaceTwistingSheaf n S) ≅ L,
      ∀ i, θ.hom.app ⊤ (pullbackSectionTop (toProjectiveSpaceOver s hs f)
          (projectiveSpaceTwistingSheaf n S)
          (pullbackSectionTop (projectiveSpaceOver.toIntegralAtUniverse n S)
            (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i))) = s i := by
  obtain ⟨α, hiso, hα⟩ := exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse s hs
  let := hiso
  set φ := toProjectiveSpaceOver s hs f with hφdef
  set q := projectiveSpaceOver.toIntegralAtUniverse n S with hqdef
  have hsnd : φ ≫ q = toProjectiveSpaceAtUniverse s hs := toProjectiveSpaceOver_snd s hs f
  refine ⟨(Scheme.Modules.pullbackComp φ q).app (twistingSheafAtUniverse.{u} n) ≪≫
      (Scheme.Modules.pullbackCongr hsnd).app (twistingSheafAtUniverse.{u} n) ≪≫ asIso α,
    fun i => ?_⟩
  have hcomp : ((Scheme.Modules.pullbackComp φ q).app
        (twistingSheafAtUniverse.{u} n)).hom.val.app (op ⊤)
      (pullbackSectionTop φ ((Scheme.Modules.pullback q).obj (twistingSheafAtUniverse.{u} n))
        (pullbackSectionTop q (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i))) =
      pullbackSectionTop (φ ≫ q) (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i) := by
    rw [← pullbackSectionTop_comp φ q (twistingSheafAtUniverse.{u} n)
      (coordGlobalSection.{u} n i)]
    exact Scheme.Modules.hom_app_inv_app
      ((Scheme.Modules.pullbackComp φ q).app (twistingSheafAtUniverse.{u} n)) (op ⊤) _
  have hcongr : ((Scheme.Modules.pullbackCongr hsnd).hom.app
        (twistingSheafAtUniverse.{u} n)).val.app (op ⊤)
      (pullbackSectionTop (φ ≫ q) (twistingSheafAtUniverse.{u} n)
        (coordGlobalSection.{u} n i)) =
      pullbackSectionTop (toProjectiveSpaceAtUniverse s hs) (twistingSheafAtUniverse.{u} n)
        (coordGlobalSection.{u} n i) :=
    pullbackSectionTop_congr hsnd (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i)
  have hfin : α.app ⊤ (pullbackSectionTop (toProjectiveSpaceAtUniverse s hs)
      (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i)) = s i := by
    rw [← pullbackCoordSection_eq (toProjectiveSpaceAtUniverse s hs) i]
    exact hα i
  calc ((Scheme.Modules.pullbackComp φ q).app (twistingSheafAtUniverse.{u} n) ≪≫
        (Scheme.Modules.pullbackCongr hsnd).app (twistingSheafAtUniverse.{u} n) ≪≫
          asIso α).hom.app ⊤
        (pullbackSectionTop φ (projectiveSpaceTwistingSheaf n S)
          (pullbackSectionTop q (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n i)))
      = α.app ⊤ (((Scheme.Modules.pullbackCongr hsnd).hom.app
            (twistingSheafAtUniverse.{u} n)).val.app (op ⊤)
          (((Scheme.Modules.pullbackComp φ q).app
              (twistingSheafAtUniverse.{u} n)).hom.val.app (op ⊤)
            (pullbackSectionTop φ (projectiveSpaceTwistingSheaf n S)
              (pullbackSectionTop q (twistingSheafAtUniverse.{u} n)
                (coordGlobalSection.{u} n i))))) := rfl
    _ = s i := by rw [hcomp, hcongr, hfin]

/-! ### Tag 0E8S -/

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **The canonical morphism of a generating family is a closed immersion**, the system it
realizes separating the closed points and the tangent vectors of `X` over `k`.

The family is not asked to separate anything by itself: what separates is the system `ψ` its
images span, and the spanning is what makes every member of `ψ` a pullback along the morphism,
which is what the criterion of [Stacks, Tag 0E8S] consumes. -/
theorem isClosedImmersion_toProjectiveSpaceOver_of_separates (p : X ⟶ Spec (.of k)) [IsProper p]
    {L : X.Modules} [IsInvertibleModule X L] {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) {ι : Type u} {ψ : ι → Γ(L, ⊤)}
    (hspan : letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
      ∀ i, ψ i ∈ Submodule.span k (Set.range s))
    (hpoints : SeparatesClosedPoints ψ) (htangent : SeparatesTangentVectors p ψ) :
    IsClosedImmersion (toProjectiveSpaceOver s hs p) := by
  classical
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  obtain ⟨θ, hθ⟩ := exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver s hs p
  have : IsProper (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) :=
    projectiveSpaceOver_isProper n (Spec (.of k))
  have hover : toProjectiveSpaceOver s hs p ≫ Stacks.Tag01VT.projectiveSpaceHom n
      (Spec (.of k)) = p := toProjectiveSpaceOver_fst s hs p
  choose U hU using fun i : ι => exists_eq_pullbackSectionTop_of_mem_span p
    (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) (toProjectiveSpaceOver s hs p) hover
    (projectiveSpaceTwistingSheaf n (Spec (.of k))) θ
    (fun j => pullbackSectionTop (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (twistingSheafAtUniverse.{u} n) (coordGlobalSection.{u} n j)) s hθ (ψ i) (hspan i)
  exact isClosedImmersion_of_separatesClosedPoints_of_separatesTangentVectors
    (toProjectiveSpaceOver s hs p) p (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k)))
    hover θ (t := U) (ψ := ψ) hU hpoints htangent

/-- **[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S).** Let `k` be an
algebraically closed field, let `X` be a proper `k`-scheme, let `ℒ` be an invertible
`𝒪_X`-module and let `V ⊂ H⁰(X, ℒ)` be a `k`-subvector space. If

1. for every pair of distinct closed points `x, y ∈ X` there is a section `s ∈ V` which vanishes
   at `x` but not at `y`, and
2. for every closed point `x ∈ X` and nonzero tangent vector `θ ∈ T_{X/k, x}` there exists a
   section `s ∈ V` which vanishes at `x` but whose pullback by `θ` is nonzero,

then `ℒ` is very ample and the canonical morphism `φ_{ℒ, V} : X ⟶ 𝐏(V)` is a closed immersion.

The conclusion is the conjunction of four assertions: `V` is finite-dimensional over `k`; `ℒ` is
very ample relative to the structure morphism; `V` generates `ℒ`, provided no closed point of `X`
is its only one; and for every basis of `V` whose family of images generates `ℒ` the canonical
morphism `φ_{ℒ, V} : X ⟶ 𝐏(V)` of [Stacks, Tag 0FCY] read in that basis is a closed immersion.

Finite-dimensionality of `V` is not assumed but derived, from [Stacks, Tag 02O6] for the
invertible module `ℒ` on the proper scheme `X`; so is generation, and so is the canonical
morphism itself, together with the identification of the pulled-back hyperplane sheaf with `ℒ`.
The side condition on the third assertion is the gap in the source's proof, discussed in the
module documentation: on a scheme with exactly one closed point condition (1) is vacuous and
`V` can generate nothing. -/
@[stacks 0E8S]
theorem isRelativelyVeryAmple_and_isClosedImmersion_toProjectiveSpaceOfModule_of_separates
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) [IsInvertibleModule X L] :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    ∀ V : Submodule k Γ(L, ⊤),
      SeparatesClosedPoints (fun v : V => (v : Γ(L, ⊤))) →
      SeparatesTangentVectors p (fun v : V => (v : Γ(L, ⊤))) →
      Module.Finite k V ∧
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple p L ∧
      ((∀ x : X, IsClosed ({x} : Set X) → ∃ y : X, IsClosed ({y} : Set X) ∧ y ≠ x) →
        GeneratesStalks (fun v : V => (v : Γ(L, ⊤)))) ∧
      ∀ (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
        (hb : GeneratesStalks fun i => ((b i : V) : Γ(L, ⊤))),
        IsClosedImmersion (toProjectiveSpaceOfModule b (fun i => ((b i : V) : Γ(L, ⊤))) hb p) := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  intro V hpoints htangent
  have : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper p L
  have hgenid : GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤)) :=
    generatesStalks_id_of_separatesClosedPoints p L hpoints
  have hpointsId : SeparatesClosedPoints (id : Γ(L, ⊤) → Γ(L, ⊤)) :=
    hpoints.mono fun v => ⟨(v : Γ(L, ⊤)), rfl⟩
  have htangentId : SeparatesTangentVectors p (id : Γ(L, ⊤) → Γ(L, ⊤)) :=
    htangent.mono p fun v => ⟨(v : Γ(L, ⊤)), rfl⟩
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · obtain ⟨m, t, hgen, hspan⟩ :=
      exists_fin_basis_generatesStalks_of_generatesStalks_id p L hgenid
    obtain ⟨θ, hθ⟩ := exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver t hgen p
    have : IsClosedImmersion (toProjectiveSpaceOver t hgen p) :=
      isClosedImmersion_toProjectiveSpaceOver_of_separates p t hgen
        (ψ := (id : Γ(L, ⊤) → Γ(L, ⊤))) hspan hpointsId htangentId
    exact Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver
      (fun m => Stacks.SymGraded.hasFreeBundleTwistOne (Spec (.of k)) m) p L
      ⟨m, toProjectiveSpaceOver t hgen p, inferInstance,
        toProjectiveSpaceOver_fst t hgen p, ⟨θ.symm⟩⟩
  · exact fun hX => generatesStalks_of_separatesClosedPoints p L hpoints hX
  · intro n b hb
    have hVspan : ∀ v : V, (v : Γ(L, ⊤)) ∈
        Submodule.span k (Set.range fun i => ((b i : V) : Γ(L, ⊤))) :=
      mem_span_range_coe_basis V b
    have : IsClosedImmersion
        (toProjectiveSpaceOver (fun i => ((b i : V) : Γ(L, ⊤))) hb p) :=
      isClosedImmersion_toProjectiveSpaceOver_of_separates p _ hb
        (ψ := fun v : V => (v : Γ(L, ⊤))) hVspan hpoints htangent
    rw [toProjectiveSpaceOfModule]
    infer_instance

/-- **[Stacks, Tag 0E8S] with the canonical morphism written out.** On a scheme no closed point
of which is its only one, condition (1) makes `V` generate `ℒ`, so the canonical morphism
`φ_{ℒ, V} : X ⟶ 𝐏(V)` of [Stacks, Tag 0FCY] exists for every basis of `V`; it is a closed
immersion, and `ℒ` is very ample.

This is the previous theorem with its third clause fed into its fourth, so that the
closed-immersion assertion is about the canonical morphism itself rather than about the
morphisms of those bases whose images happen to generate. The side condition is the one the
source's proof needs and does not state; see the module documentation. -/
theorem isClosedImmersion_toProjectiveSpaceOfModule_of_separates (p : X ⟶ Spec (.of k))
    [IsProper p] (L : X.Modules) [IsInvertibleModule X L] :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    ∀ (V : Submodule k Γ(L, ⊤))
      (hpoints : SeparatesClosedPoints (fun v : V => (v : Γ(L, ⊤)))),
      SeparatesTangentVectors p (fun v : V => (v : Γ(L, ⊤))) →
      ∀ (hX : ∀ x : X, IsClosed ({x} : Set X) → ∃ y : X, IsClosed ({y} : Set X) ∧ y ≠ x)
      (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V),
      IsClosedImmersion (toProjectiveSpaceOfModule b (fun i => ((b i : V) : Γ(L, ⊤)))
        (generatesStalks_fin_of_mem_span p L (fun i => ((b i : V) : Γ(L, ⊤)))
          (fun v : V => (v : Γ(L, ⊤)))
          (generatesStalks_of_separatesClosedPoints p L hpoints hX)
          (mem_span_range_coe_basis V b)) p) := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  intro V hpoints htangent hX n b
  exact (isRelativelyVeryAmple_and_isClosedImmersion_toProjectiveSpaceOfModule_of_separates p L V
    hpoints htangent).2.2.2 n b _

end AlgebraicGeometry

end
