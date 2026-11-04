module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FlatOfPushforward
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.StructureSheaf
public import StacksFrontier.RingTheory.Flat.GradedInjectiveFlat

/-!
# Running the filtration ladder on the sections of a direct image

The kernels on sections of the comparisons `𝒪_V ⟶ g_*(𝒪_U/𝔪ⁿ𝒪_U)` are a filtration of the
sections of `𝒪_V` of the kind `Stacks.Flatness.flat_and_eq_smul_top_of_ladder` consumes.  Running
that ladder one affine open of `V` at a time proves the sentence of [Stacks, Tag 0E3X] reading
*"reading the references given above backwards (and using induction) one concludes that `𝒪_V` is
flat over `A` with reduction `𝒪_V/𝔪_A 𝒪_V = 𝒪_Y`"* — in the form: the sections of `𝒪_V` over an
affine open are a flat `A`-module, and the kernel of the comparison at `n = 1` on them is `𝔪`
times the sections.

The filtration fed to the ladder is the family of kernels

```
K n = { s ∈ Γ(V, O) | (𝒪_V ⟶ g_*(𝒪_U/𝔪ⁿ𝒪_U))(s) = 0 }
```

an `A`-submodule because the comparison carries an `A`-scalar into multiplication by the global
function the scalar determines on `V`.

## Main results

* `Stacks.BaseAdicFiltration.app_pushforwardAdicProj_smul`: the comparison moves an `A`-scalar
  across into multiplication by the global function the scalar determines on `V`.
* `Stacks.BaseAdicFiltration.flat_sections_and_app_pushforwardAdicProj_one_eq_zero_iff`: **the
  ladder**, run on the sections over one affine open.
* `Stacks.BaseAdicFiltration.flat_of_pushforwardAdicProj`: `pV` is flat.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0AS8](https://stacks.math.columbia.edu/tag/0AS8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

namespace Stacks.BaseAdicFiltration

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] hasFiniteBiproducts_schemeModules

variable {A : Type u} [CommRing A] {U V : Scheme.{u}}
  (p : U ⟶ Spec (CommRingCat.of A)) (pV : V ⟶ Spec (CommRingCat.of A))

/-- **The comparison carries an `A`-scalar into multiplication by a global function.**  For
`a : A` and a section `s` of `𝒪_V`, the comparison of `a • s` is multiplication by the function
`a` determines on `V`, applied to the comparison of `s`.

This is `Stacks.BaseAdicFiltration.sectionSmul_naturality` read on sections. -/
theorem app_pushforwardAdicProj_smul (g : U ⟶ V) (I : Ideal A) (n : ℕ) (a : A) (O : V.Opens)
    (s : Γ(V, O)) :
    letI := sectionsAlgebra pV O
    (pushforwardAdicProj p g I n).app O (a • s) =
      (sectionSmul (baseScalarMap pV a) ((Scheme.Modules.pushforward g).obj
        (adicQuotient p I n (Scheme.unitModule U)))).app O
          ((pushforwardAdicProj p g I n).app O s) := by
  let := sectionsAlgebra pV O
  exact congrArg (fun φ : Scheme.unitModule V ⟶ (Scheme.Modules.pushforward g).obj
        (adicQuotient p I n (Scheme.unitModule U)) =>
      Scheme.Modules.Hom.app φ O (s : Γ(Scheme.unitModule V, O)))
    (sectionSmul_naturality (baseScalarMap pV a) (pushforwardAdicProj p g I n))

/-- **The kernel of the comparison on the sections over an open, as an `A`-submodule.**  Additive
because the comparison is additive, and stable under the `A`-action by
`Stacks.BaseAdicFiltration.app_pushforwardAdicProj_smul`: the scalar becomes multiplication by a
global function, which kills zero. -/
def pushforwardAdicProjKer (g : U ⟶ V) (I : Ideal A) (n : ℕ) (O : V.Opens) :
    letI := sectionsAlgebra pV O
    Submodule A Γ(V, O) :=
  letI := sectionsAlgebra pV O
  { carrier := {s : Γ(V, O) | (pushforwardAdicProj p g I n).app O s = 0}
    add_mem' := fun {x y} hx hy => by
      have hx' : (pushforwardAdicProj p g I n).app O x = 0 := hx
      have hy' : (pushforwardAdicProj p g I n).app O y = 0 := hy
      have hadd : (pushforwardAdicProj p g I n).app O (x + y) =
          (pushforwardAdicProj p g I n).app O x +
            (pushforwardAdicProj p g I n).app O y := map_add _ _ _
      change (pushforwardAdicProj p g I n).app O (x + y) = 0
      rw [hadd, hx', hy', add_zero]
    zero_mem' := by
      change (pushforwardAdicProj p g I n).app O 0 = 0
      exact map_zero _
    smul_mem' := fun a x hx => by
      have hx' : (pushforwardAdicProj p g I n).app O x = 0 := hx
      change (pushforwardAdicProj p g I n).app O (a • x) = 0
      rw [app_pushforwardAdicProj_smul p pV g I n a O x, hx']
      exact map_zero _ }

/-- A section of `𝒪_V` lies in the kernel submodule exactly when the comparison kills it. -/
@[simp]
theorem mem_pushforwardAdicProjKer (g : U ⟶ V) (I : Ideal A) (n : ℕ) (O : V.Opens)
    (s : Γ(V, O)) :
    letI := sectionsAlgebra pV O
    s ∈ pushforwardAdicProjKer p pV g I n O ↔
      (pushforwardAdicProj p g I n).app O s = 0 :=
  Iff.rfl

/-- The graded-piece comparison for `𝒪_U`, built from the special-fibre identification, is an
isomorphism. -/
private theorem isIso_gradedDesc_specialFibreIso [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat p] (n : ℕ) {k : ℕ}
    (e₀ : (↥(IsLocalRing.maximalIdeal A ^ n) ⧸
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A ↥(IsLocalRing.maximalIdeal A ^ n)))) ≃ₗ[A]
        (Fin k → (A ⧸ IsLocalRing.maximalIdeal A)))
    (x : Fin k → ↥(IsLocalRing.maximalIdeal A ^ n))
    (hxs : ∀ i, e₀.symm (Pi.single i (1 : A ⧸ IsLocalRing.maximalIdeal A)) =
      Submodule.Quotient.mk (x i)) :
    IsIso (C := U.Modules) (gradedDesc p (IsLocalRing.maximalIdeal A) n (Scheme.unitModule U)
      (fun i => (x i : A)) (fun i => (x i).2)
      (specialFibreIso p (IsLocalRing.maximalIdeal A) n (Scheme.unitModule U)).1) :=
  isIso_gradedDesc p _ n (Scheme.unitModule U) (flatStalks_unit p) e₀ x hxs _
    (specialFibreIso p _ n (Scheme.unitModule U)).2

/-- **The decomposition step of the ladder.**  A section of `𝒪_V` killed by the comparison at `n`
is the sum of a section in `𝔪ⁿ Γ(V, 𝒪)` and a section killed by the comparison at `n + 1`.

Choose representatives `aᵢ ∈ 𝔪ⁿ` of a `κ`-basis of `𝔪ⁿ/𝔪ⁿ⁺¹`
(`Stacks.Flatness.exists_pi_linearEquiv_gradedPiece`); then
`Stacks.BaseAdicFiltration.exists_sum_smul_app_pushforwardAdicProj_succ_eq_zero`, whose
identification of the graded piece is `Stacks.BaseAdicFiltration.isIso_gradedDesc`, writes `s` as
`∑ aᵢ mᵢ` plus a section the comparison at `n + 1` kills. -/
private theorem pushforwardAdicProjKer_le_sup_smul_top [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat p] {g : U ⟶ V} (hg : g ≫ pV = p)
    (hSE : ∀ n, ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
      (Scheme.unitModule U)).map (Scheme.Modules.pushforward g)).ShortExact)
    (O : V.Opens)
    (hsurj : Function.Surjective
      ((pushforwardAdicProj p g (IsLocalRing.maximalIdeal A) 1).app O)) (n : ℕ) :
    letI := sectionsAlgebra pV O
    pushforwardAdicProjKer p pV g (IsLocalRing.maximalIdeal A) n O ≤
      IsLocalRing.maximalIdeal A ^ n • (⊤ : Submodule A Γ(V, O)) ⊔
        pushforwardAdicProjKer p pV g (IsLocalRing.maximalIdeal A) (n + 1) O := by
  classical
  let := sectionsAlgebra pV O
  set 𝔪 := IsLocalRing.maximalIdeal A
  intro s hs
  have hs' : (pushforwardAdicProj p g 𝔪 n).app O s = 0 := hs
  obtain ⟨k, ⟨e₀⟩⟩ := Stacks.Flatness.exists_pi_linearEquiv_gradedPiece 𝔪 n
  choose x hx using fun i : Fin k =>
    Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule A ↥(𝔪 ^ n)))
      (e₀.symm (Pi.single i (1 : A ⧸ 𝔪)))
  have hxs : ∀ i, e₀.symm (Pi.single i (1 : A ⧸ 𝔪)) = Submodule.Quotient.mk (x i) :=
    fun i => (hx i).symm
  obtain ⟨m, hm⟩ := exists_sum_smul_app_pushforwardAdicProj_succ_eq_zero p pV hg 𝔪 n
    (fun i => (x i : A)) (fun i => (x i).2)
    (specialFibreIso p 𝔪 n (Scheme.unitModule U)).1
    (specialFibreIso p 𝔪 n (Scheme.unitModule U)).2
    (isIso_gradedDesc_specialFibreIso p n e₀ x hxs)
    (hSE n) O hsurj s hs'
  refine Submodule.mem_sup.2 ⟨∑ i, (x i : A) • m i, ?_, s - ∑ i, (x i : A) • m i, hm, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (x i).2 Submodule.mem_top
  · exact add_sub_cancel _ _

/-- **The ladder of [Stacks, Tag 0E3X], run on the sections over one affine open.**  Let
`p : U ⟶ Spec A` be flat over an Artinian local base, `g : U ⟶ V` a morphism over `Spec A` with
`𝒪_V = g_*𝒪_U`, and suppose the direct images of the filtration sequences of `𝒪_U` are short
exact and that `g_*(𝒪_U/𝔪𝒪_U)` is quasi-coherent.  Then the sections of `𝒪_V` over an affine open
form a flat `A`-module, and the kernel of the comparison `𝒪_V ⟶ g_*(𝒪_U/𝔪𝒪_U)` on them is `𝔪`
times the sections.

The identification of the graded piece that the ladder's `hgr` needs is
`Stacks.BaseAdicFiltration.isIso_gradedDesc`, whose flatness input is
`Stacks.BaseAdicFiltration.flatStalks_unit`. -/
theorem flat_sections_and_app_pushforwardAdicProj_one_eq_zero_iff [IsArtinianRing A]
    [IsLocalRing A] [AlgebraicGeometry.Flat p] {g : U ⟶ V} (hg : g ≫ pV = p)
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (N : ℕ) (hN : IsLocalRing.maximalIdeal A ^ (N + 1) = ⊥)
    (hSE : ∀ n, ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
      (Scheme.unitModule U)).map (Scheme.Modules.pushforward g)).ShortExact)
    (hqc : ((Scheme.Modules.pushforward g).obj
      (adicQuotient p (IsLocalRing.maximalIdeal A) 1 (Scheme.unitModule U))).IsQuasicoherent)
    (O : V.Opens) (hO : IsAffineOpen O) :
    letI := sectionsAlgebra pV O
    Module.Flat A Γ(V, O) ∧
      ∀ s : Γ(V, O),
        (pushforwardAdicProj p g (IsLocalRing.maximalIdeal A) 1).app O s = 0 ↔
          s ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A Γ(V, O)) := by
  classical
  let := sectionsAlgebra pV O
  set 𝔪 := IsLocalRing.maximalIdeal A
  set K : ℕ → Submodule A Γ(V, O) := fun n => pushforwardAdicProjKer p pV g 𝔪 n O
  -- the base case: at the top of the filtration the comparison is injective
  have hKbot : K (N + 1) = ⊥ := by
    refine le_antisymm (fun s hs => ?_) bot_le
    have hs' : (pushforwardAdicProj p g 𝔪 (N + 1)).app O s = 0 := hs
    have hinj := injective_app_pushforwardAdicProj_of_pow_eq_bot p g hc 𝔪 hN O
    exact hinj (hs'.trans (map_zero _).symm)
  -- the easy containment: `𝔪ⁿ` kills the target
  have hle : ∀ n, 𝔪 ^ n • (⊤ : Submodule A Γ(V, O)) ≤ K n := fun n =>
    Submodule.smul_le.2 fun a ha x _ =>
      smul_app_pushforwardAdicProj_eq_zero p pV hg 𝔪 n ha O x
  -- the cohomological input: the comparison at `n = 1` is surjective on sections
  have hsurj : Function.Surjective ((pushforwardAdicProj p g 𝔪 1).app O) :=
    surjective_app_pushforwardAdicProj p g hc 𝔪 N hN hSE 1 (by omega) hqc O hO
  -- the decomposition step
  have hsup : ∀ n, K n ≤ 𝔪 ^ n • (⊤ : Submodule A Γ(V, O)) ⊔ K (n + 1) :=
    pushforwardAdicProjKer_le_sup_smul_top p pV hg hSE O hsurj
  -- the graded condition
  have hgr : ∀ n, 1 ≤ n → n ≤ N →
      ∀ {k : ℕ} (e₀ : (↥(𝔪 ^ n) ⧸ (𝔪 • (⊤ : Submodule A ↥(𝔪 ^ n)))) ≃ₗ[A] (Fin k → (A ⧸ 𝔪)))
        (x : Fin k → ↥(𝔪 ^ n)),
        (∀ i, e₀.symm (Pi.single i (1 : A ⧸ 𝔪)) = Submodule.Quotient.mk (x i)) →
        ∀ m : Fin k → Γ(V, O), (∑ i, (x i : A) • m i) ∈ K (n + 1) → ∀ i, m i ∈ K 1 := by
    intro n _ _ k e₀ x hxs m hm i
    exact app_pushforwardAdicProj_one_eq_zero_of_sum_smul p pV hg 𝔪 n
      (fun i => (x i : A)) (fun i => (x i).2)
      (specialFibreIso p 𝔪 n (Scheme.unitModule U)).1
      (specialFibreIso p 𝔪 n (Scheme.unitModule U)).2
      (isIso_gradedDesc_specialFibreIso p n e₀ x hxs)
      O m hm i
  obtain ⟨hflat, hone⟩ :=
    Stacks.Flatness.flat_and_eq_smul_top_of_ladder 𝔪 Γ(V, O) K N hN hKbot hle hsup hgr
  refine ⟨hflat, fun s => ?_⟩
  constructor
  · intro hs
    exact hone ▸ (show s ∈ K 1 from hs)
  · intro hs
    exact (hone ▸ hs : s ∈ K 1)

/-- **The constructed family is flat.**  `Stacks.BaseAdicFiltration.flat_of_flat_sections`
applied to the flatness half of
`Stacks.BaseAdicFiltration.flat_sections_and_app_pushforwardAdicProj_one_eq_zero_iff`. -/
theorem flat_of_pushforwardAdicProj [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat p] {g : U ⟶ V} (hg : g ≫ pV = p)
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (N : ℕ) (hN : IsLocalRing.maximalIdeal A ^ (N + 1) = ⊥)
    (hSE : ∀ n, ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
      (Scheme.unitModule U)).map (Scheme.Modules.pushforward g)).ShortExact)
    (hqc : ((Scheme.Modules.pushforward g).obj
      (adicQuotient p (IsLocalRing.maximalIdeal A) 1 (Scheme.unitModule U))).IsQuasicoherent) :
    AlgebraicGeometry.Flat pV :=
  flat_of_flat_sections pV fun W =>
    (flat_sections_and_app_pushforwardAdicProj_one_eq_zero_iff p pV hg hc N hN hSE hqc
      W.1 W.2).1

end Stacks.BaseAdicFiltration

end
