module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ChartTwistOne
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoGeneration

/-!
# Very ampleness from the degree-two hypothesis

Let `k` be an algebraically closed field, let `X` be proper over `k` through `p` and let `ℒ` be
an invertible module on `X`. If `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every closed
subscheme `Z ⊆ X` of dimension zero and degree two over `k`, then `ℒ` is very ample over `k`.
That is [Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T), and this file completes
its proof: nothing below assumes the morphism to projective space, the identification of the
pulled-back twist, or completeness of the linear system.

The route is the source's. The degree-two hypothesis makes the global sections of `ℒ` generate
it, which is
`AlgebraicGeometry.generatesStalks_id_of_surjectsOnDegreeTwo` in the companion file; `H⁰(X, ℒ)`
is finite-dimensional over `k` by [Stacks, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6),
so a basis of it is a finite generating family, and being a basis it spans — which is what makes
the linear system the morphism realizes *complete*, as the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) requires. The pairs of distinct
closed points and the fat points supply that criterion's two separation conditions, so the
morphism is a closed immersion, and projective space over the affine base `Spec k` is the
projective bundle of a free module, which is the datum relative very ampleness asks for.

## Main results

* `AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo'`: **Tag 0E8T in full**, with
  no assumed data.
* `AlgebraicGeometry.exists_isClosedImmersion_of_surjectsOnDegreeTwo`: the morphism of
  [Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY) attached to a basis of
  `H⁰(X, ℒ)` is a closed immersion `X ⟶ ℙⁿ_k` over `k`, with `φ^* 𝒪(1) ≅ ℒ`.
* `AlgebraicGeometry.isClosedImmersion_of_pinned_of_span`: the same with the morphism, the twist
  isomorphism and a spanning family given — the abstract step behind it.

## The `k`-linear ingredients

* `AlgebraicGeometry.pullbackSectionTop_smul`: pulling back a global section is semilinear over
  the pullback of functions. This is linearity of the component of the unit of the
  pullback--pushforward adjunction; the scalars of the pushforward are restricted along `f` on
  the nose, so the two actions agree definitionally once both are spelled at `Γ(-, ⊤)`.
* `AlgebraicGeometry.moduleFinite_sections_of_isProper`: **Tag 02O6 for an invertible module on
  a proper scheme over a field** — `H⁰(X, ℒ)` is a finite-dimensional `k`-vector space, the
  `k`-structure being the one `AlgebraicGeometry.baseRingMap` gives.
* `AlgebraicGeometry.generatesStalks_of_span_eq_top`: a family of global sections spanning
  `H⁰(X, ℒ)` over `k` generates `ℒ` as soon as the complete system does. Vanishing at a point is
  a `k`-linear condition because the germ map is semilinear.
* `AlgebraicGeometry.exists_eq_pullbackSectionTop_of_span`: if the images of a family of
  sections of `ℳ` span `H⁰(X, ℒ)` over `k`, then *every* global section of `ℒ` is the image of
  one — the image of pullback-and-transport is a `k`-submodule. This is completeness.
* `AlgebraicGeometry.exists_fin_basis_generatesStalks`: a basis of `H⁰(X, ℒ)`, padded with the
  zero section to be indexed by `Fin (n + 1)`, generates `ℒ` and spans `H⁰(X, ℒ)`.

## Implementation notes

**Why the `show` in `AlgebraicGeometry.pullbackSectionTop_smul`.** The scalar action on sections
is registered for the `Γ(M, U)` spelling of Mathlib's `AlgebraicGeometry.Scheme.Modules.presheaf`,
while `AlgebraicGeometry.pullbackSectionTop` is stated at `M.val.obj (op ⊤)`. The two types are
definitionally equal but instance search does not cross between them, so `a • pullbackSectionTop
f M s` does not elaborate; the ascription puts the scalar action back in the spelling where the
instance lives.

**Why `AlgebraicGeometry.pullbackGlobalSections_eq_pullbackSectionTop` writes its equality of
opens as `rfl`.** The two spellings of the pullback of a global section differ by
`presheaf.map (eqToHom _).op`, and the `eqToHom` is the identity because `f ⁻¹ᵁ ⊤` is `⊤`. With
the equality supplied by a tactic the comparison is checked against an opaque proof and exhausts
the heartbeat budget; written as `rfl` it reduces, and `CategoryTheory.Functor.map_id_apply`
closes the goal. The same argument is already inside the proof of
`Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections`.

**The index types.** `Stacks.ProjectiveFromSections.GeneratesStalks` is used here at both
`Fin (n + 1)` and a `Type u` index; `Stacks.ProjectiveFromSections.generatesStalks_ulift_iff`
moves between them.

## References

* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
* [Stacks Project, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Ample (IsInvertibleModule)

universe u

namespace AlgebraicGeometry

/-! ### The base field acting on sections -/

/-- The ring map `k ⟶ Γ(X, 𝒪_X)` attached to a `k`-scheme, through which the base field acts on
the sections of every module on `X`. -/
abbrev baseRingMap {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom

/-- **Pulling back a global section is semilinear**: the pullback of `a • s` is the pullback of
`a` as a function acting on the pullback of `s`. This is linearity of the component of the unit
of the pullback--pushforward adjunction, the scalars on the pushforward being restricted along
`f` on the nose. -/
theorem pullbackSectionTop_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (a : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    pullbackSectionTop f M (a • s) =
      f.appTop a •
        (show Γ((Scheme.Modules.pullback f).obj M, ⊤) from pullbackSectionTop f M s) :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) a s

/-- Pulling back the zero section gives the zero section. -/
theorem pullbackSectionTop_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    pullbackSectionTop f M 0 = 0 :=
  map_zero _

/-- Pulling back global sections is additive. -/
theorem pullbackSectionTop_add {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s t : M.val.obj (op ⊤)) :
    pullbackSectionTop f M (s + t) =
      pullbackSectionTop f M s + pullbackSectionTop f M t :=
  map_add _ _ _

/-- The base field acts on the sections of a module over a `k`-scheme through
`AlgebraicGeometry.baseRingMap`. -/
theorem baseRingMap_comp {k : Type u} [Field k] {X P : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : P ⟶ Spec (.of k)) (φ : X ⟶ P) (hφ : φ ≫ q = p) (c : k) :
    φ.appTop (baseRingMap q c) = baseRingMap p c := by
  have h : ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ φ.appTop) = (Scheme.ΓSpecIso (.of k)).inv ≫
      (φ ≫ q).appTop := by
    rw [Scheme.Hom.comp_appTop]
  exact congrArg (fun g : CommRingCat.of k ⟶ Γ(X, ⊤) => g.hom c) (h.trans (by rw [hφ]))

/-! ### Finite-dimensionality of the space of global sections -/

/-- **[Stacks, Tag 02O6] for an invertible module on a proper scheme over a field**: its space of
global sections is finite-dimensional over the base field. An invertible module on a locally
Noetherian scheme is coherent, Tag 02O6 makes the degree-zero cohomology a finite module over
`Γ(Spec k, ⊤)`, and that ring is the base field. -/
theorem moduleFinite_sections_of_isProper {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) [IsInvertibleModule X L] :
    @Module.Finite k Γ(L, ⊤) _ _ (Module.compHom _ (baseRingMap p)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one X L).mpr
      (Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X L)
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have h := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology p L 0
  let : Module Γ(Spec (CommRingCat.of k), ⊤) Γ(L, ⊤) := Module.compHom _ p.appTop.hom
  have : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(L, ⊤) :=
    Module.Finite.equiv ((ModuleCat.restrictScalars p.appTop.hom).mapIso
      ((Functor.rightDerivedZeroIsoSelf
        (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).app L)).toLinearEquiv
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2 Γ(L, ⊤)

/-! ### A spanning family generates -/

/-- **A family of global sections spanning `H⁰(X, ℒ)` over `k` generates `ℒ` as soon as the
complete system does.** Vanishing at a point is a `k`-linear condition: the sections whose germ
at `x` lies in `𝔪ₓ · ℒₓ` form a submodule, because the germ map is semilinear and the base
field acts through `Γ(X, 𝒪_X)`. -/
theorem generatesStalks_of_span_eq_top {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : X.Modules) [IsInvertibleModule X L] {ι : Type u}
    (t : ι → Γ(L, ⊤))
    (hspan : letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
      ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range t))
    (hgen : Stacks.ProjectiveFromSections.GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤))) :
    Stacks.ProjectiveFromSections.GeneratesStalks t := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  refine generatesStalks_of_forall_exists_mem_nonvanishingLocus L t fun z => ?_
  by_contra hz
  push Not at hz
  have hvanish : ∀ i, (L.presheaf.Γgerm z).hom (t i) ∈ Stacks.ModuleStalk.maximalSmul L z := by
    intro i
    have := hz i
    rwa [Stacks.Ample.mem_nonvanishingLocus_iff, not_not] at this
  have hsub : ∀ σ ∈ Submodule.span k (Set.range t),
      (L.presheaf.Γgerm z).hom σ ∈ Stacks.ModuleStalk.maximalSmul L z := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hvanish i
    | zero => simp
    | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [show (c • a : Γ(L, ⊤)) = baseRingMap p c • a from rfl, Stacks.ModuleStalk.Γgerm_smul]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨s, hs⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks
    (id : Γ(L, ⊤) → Γ(L, ⊤)) hgen z
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, Stacks.Ample.mem_nonvanishingLocus_iff] at hs
  exact hs (hsub s (hspan s))

/-! ### Completeness of the realized system -/

/-- **A family of sections upstairs whose images span `H⁰(X, ℒ)` realizes the complete linear
system.** Pulling back along `φ` and transporting along `θ` is additive and carries the action
of `k` on the sections upstairs to its action downstairs, so its image is a `k`-submodule; if it
contains a spanning family it is everything. -/
theorem exists_eq_pullbackSectionTop_of_span {k : Type u} [Field k] {X P : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : P ⟶ Spec (.of k)) (φ : X ⟶ P) (hφ : φ ≫ q = p)
    (M : P.Modules) {L : X.Modules} (θ : (Scheme.Modules.pullback φ).obj M ≅ L)
    {ι : Type u} (T : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤))
    (hpin : ∀ i, θ.hom.app ⊤ (pullbackSectionTop φ M (T i)) = t i)
    (hspan : letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
      ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range t)) (σ : Γ(L, ⊤)) :
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
  have hmem : ∀ σ ∈ Submodule.span k (Set.range t),
      ∃ u : Γ(M, ⊤), θ.hom.app ⊤ (pullbackSectionTop φ M u) = σ := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨T i, hpin i⟩
    | zero => exact ⟨0, (congrArg _ (pullbackSectionTop_zero φ M)).trans (map_zero _)⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, ((congrArg _ (pullbackSectionTop_add φ M u v)).trans (map_add _ _ _)).trans
        (congrArg₂ _ hu hv)⟩
    | smul c a _ ha =>
      obtain ⟨u, hu⟩ := ha
      exact ⟨c • u, by rw [hΦsmul c u, hu]⟩
  exact hmem σ (hspan σ)

/-! ### A basis of the complete system, as a generating family -/

/-- **The degree-two hypothesis produces a finite family of global sections which generates `ℒ`
and spans `H⁰(X, ℒ)` over `k`.** A basis of the finite-dimensional space `H⁰(X, ℒ)`, padded with
the zero section so that it is indexed by `Fin (n + 1)`, does both: it spans by construction, and
it generates because the complete system does and vanishing at a point is `k`-linear.

This is the family the morphism to `ℙⁿ_k` of
`AlgebraicGeometry.exists_hom_projectiveSpaceOver_of_surjectsOnDegreeTwo` should be built from:
being a basis, it makes the realized linear system complete, which is what the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) asks. -/
theorem exists_fin_basis_generatesStalks {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) [IsInvertibleModule X L]
    (hsurj : SurjectsOnDegreeTwo p L) :
    letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    ∃ (n : ℕ) (t : Fin (n + 1) → Γ(L, ⊤)),
      Stacks.ProjectiveFromSections.GeneratesStalks t ∧
      ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range t) := by
  classical
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  have : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper p L
  let b := Module.finBasis k Γ(L, ⊤)
  have hb : ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k
      (Set.range (Fin.lastCases (0 : Γ(L, ⊤)) fun j => b j : Fin (Module.finrank k Γ(L, ⊤) + 1) →
        Γ(L, ⊤))) := fun σ => by
    refine Submodule.span_mono ?_ (b.mem_span σ)
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castSucc j, by simp⟩
  refine ⟨_, _, ?_, hb⟩
  rw [← Stacks.ProjectiveFromSections.generatesStalks_ulift_iff]
  refine generatesStalks_of_span_eq_top p L _ (fun σ => ?_)
    (generatesStalks_id_of_surjectsOnDegreeTwo p L hsurj)
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (hb σ)

/-! ### The two spellings of the pullback of a global section -/

/-- **`AlgebraicGeometry.pullbackGlobalSections` is `AlgebraicGeometry.pullbackSectionTop`.** The
former post-composes the unit of the adjunction with the restriction along `f ⁻¹ᵁ ⊤ = ⊤`, which
is the identity.

The proof of `Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections` is where
this argument appears; what makes it cheap is writing the equality of opens as `rfl` inside the
`eqToHom`, so that the comparison reduces instead of being checked against an opaque proof. -/
theorem pullbackGlobalSections_eq_pullbackSectionTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    pullbackGlobalSections f M s = pullbackSectionTop f M s := by
  show ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op (pullbackSectionTop f M s) = _
  exact Functor.map_id_apply _ _ _

/-- The pulled-back homogeneous coordinate is the pullback of the homogeneous coordinate. -/
theorem pullbackCoordSection_eq {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) :
    Stacks.TwistPullbackPinned.pullbackCoordSection g i =
      pullbackSectionTop g (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)
        (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n i) :=
  pullbackGlobalSections_eq_pullbackSectionTop g _ _

/-! ### The closed immersion -/

/-- **A morphism realizing a `k`-spanning family of sections of an invertible `ℒ` is a closed
immersion**, under the degree-two hypothesis. The family being spanning makes the realized
system complete, which is what the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) asks of it. -/
theorem isClosedImmersion_of_pinned_of_span {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] (q : Y ⟶ Spec (.of k)) [IsSeparated q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p) (M : Y.Modules) (L : X.Modules) [IsInvertibleModule X L]
    (θ : (Scheme.Modules.pullback φ).obj M ≅ L) {ι : Type u} (T : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤))
    (hpin : ∀ i, θ.hom.app ⊤ (pullbackSectionTop φ M (T i)) = t i)
    (hspan : letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
      ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range t))
    (hsurj : SurjectsOnDegreeTwo p L) : IsClosedImmersion φ := by
  classical
  choose U hU using fun σ : Γ(L, ⊤) =>
    exists_eq_pullbackSectionTop_of_span p q φ hφ M θ T t hpin hspan σ
  exact isClosedImmersion_of_surjectsOnDegreeTwo φ p q hφ θ (t := U) (ψ := id) hU
    Function.surjective_id hsurj

/-! ### The morphism to projective space, and very ampleness -/

/-- **The degree-two hypothesis makes `X` a closed subscheme of a projective space over `k`,
with no assumed data.** A basis of `H⁰(X, ℒ)` generates `ℒ`, so it gives a morphism
`φ : X ⟶ ℙⁿ_k` over `k` and an isomorphism `φ^* 𝒪(1) ≅ ℒ` carrying the homogeneous coordinates
to the basis; being a basis, it makes the realized linear system complete, and the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) — whose two separation hypotheses
the degree-two hypothesis supplies — makes `φ` a closed immersion. -/
theorem exists_isClosedImmersion_of_surjectsOnDegreeTwo {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules)
    [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L) :
    ∃ (n : ℕ) (φ : X ⟶ projectiveSpaceOver n (Spec (.of k))),
      IsClosedImmersion φ ∧
      φ ≫ Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k)) = p ∧
      Nonempty ((Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅ L) := by
  classical
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  obtain ⟨n, t, hgen, hspan⟩ := exists_fin_basis_generatesStalks p L hsurj
  obtain ⟨φ, hφ, α, hiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse t hgen p
  let := hiso
  have : IsProper (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) :=
    projectiveSpaceOver_isProper n (Spec (.of k))
  let g := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))
  let e := (Scheme.Modules.pullbackComp φ g).app
    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n) ≪≫ asIso α
  refine ⟨n, φ, ?_, hφ, ⟨e⟩⟩
  refine isClosedImmersion_of_pinned_of_span p
    (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) φ hφ _ L e
    (fun i : ULift.{u} (Fin (n + 1)) =>
      Stacks.TwistPullbackPinned.pullbackCoordSection g i.down)
    (fun i : ULift.{u} (Fin (n + 1)) => t i.down) (fun i => ?_) (fun σ => ?_) hsurj
  · rw [← hα i.down, pullbackCoordSection_eq, pullbackCoordSection_eq,
      ← pullbackSectionTop_comp φ g (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n)
        (Stacks.TwistPullbackPinned.coordGlobalSection n i.down)]
    exact congrArg (fun y => (Scheme.Modules.Hom.app α ⊤) y)
      (Scheme.Modules.hom_app_inv_app ((Scheme.Modules.pullbackComp φ g).app
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n)) (op ⊤) _)
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (hspan σ)

/-- **[Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T).** Let `k` be an
algebraically closed field, let `X` be a proper `k`-scheme and let `ℒ` be an invertible
`𝒪_X`-module. If `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every closed subscheme `Z ⊆ X` of
dimension zero and degree two over `k`, then `ℒ` is very ample on `X` over `k`.

The pairs of distinct closed points and the fat points among those subschemes give the two
separation conditions of [Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S); the same
hypothesis makes the global sections generate `ℒ`, so a basis of the finite-dimensional space
`H⁰(X, ℒ)` defines a morphism to `ℙⁿ_k` realizing the complete linear system, and that morphism
is a closed immersion. Projective space over the affine base is the projective bundle of a free
module, which turns the immersion into the datum relative very ampleness asks for. -/
@[stacks 0E8T "the full statement, with no assumed data: the dimension of a \
zero-dimensional closed subscheme is the topological Krull dimension of its space and \
its degree is the dimension over k of its ring of global sections"]
theorem isRelativelyVeryAmple_of_surjectsOnDegreeTwo' {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules)
    [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple p L := by
  obtain ⟨n, φ, hci, hφ, ⟨e⟩⟩ := exists_isClosedImmersion_of_surjectsOnDegreeTwo p L hsurj
  have := hci
  exact Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver
    (fun m => Stacks.SymGraded.hasFreeBundleTwistOne (Spec (.of k)) m) p L
    ⟨n, φ, inferInstance, hφ, ⟨e.symm⟩⟩

end AlgebraicGeometry

end
