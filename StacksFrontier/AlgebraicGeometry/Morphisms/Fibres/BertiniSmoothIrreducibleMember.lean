module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Connected
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPrimeThroughPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.ImmersionCover

/-!
# A smooth irreducible hyperplane section

**[Stacks, Tag 0G4G].** Let `k` be an algebraically closed field and let `X ⊂ 𝐏^n_k` be smooth
and irreducible of dimension `≥ 2`. Then there is a hyperplane `H ⊂ 𝐏^n_k` such that `X ∩ H` is
smooth and irreducible.

The data `X ⊂ 𝐏^n_k` is the standing situation of the Bertini theorems
([Stacks, Tag 0G47], `Stacks.Bertini.FamilyDivisors`): the linear system
`V = k T_0 ⊕ … ⊕ k T_n` of the remark is the vector space `V` of the situation, `ψ : V → Γ(X, L)`
is the restriction of the coordinates to `X` with `L = 𝒪_X(1)`, and the hyperplane section
`X ∩ H_v` is the divisor `H_v = Z(ψ(v))`, which over the base field itself is
`Stacks.Bertini.FamilyDivisors.specializedDivisor` at `K = k`. The inclusion
`X ⊂ 𝐏^n_k` is read, as in [Stacks, Tag 0FD6], as hypotheses (2) and (3) of that tag — the
image of `ψ` generates `L`, and the morphism `φ_{L,ψ} : X → 𝐏(V)` it determines is an
immersion — together with properness of `X` over `k`, which says the immersion is a *closed*
one. Nothing further about the embedding is assumed: ampleness of `L`, which is what
Enriques–Severi–Zariski needs, is derived from those data below.

## Main results

* `Stacks.Bertini.ProjectiveSubscheme.exists_hyperplane_smooth_irreducibleSpace`: **the tag**,
  for a closed subscheme `X ⊂ ℙⁿ_k`: some nonzero linear form `∑ⱼ cⱼ Tⱼ` cuts out a hyperplane
  `H` with `X ∩ H` smooth over `k` and irreducible.
* `Stacks.Bertini.FamilyDivisors.exists_smooth_irreducibleSpace_specializedDivisor`: the tag in
  the standing situation of an arbitrary finite dimensional linear system. There is a coordinate
  tuple `c` over `k` such that the vector `v = ∑ᵢ cᵢ vᵢ` has
  `ψ(v) ≠ 0` — so `H_v` is a genuine divisor and not all of `X` — and `H_v` is smooth over `k`
  and irreducible.
* `Stacks.Bertini.FamilyDivisors.exists_smooth_irreducibleSpace_specializedDivisor_of_coheight`:
  the same with `dim X ≥ 2` read at the closed points, the form [Stacks, Tag 0FD9] consumes.
* `Stacks.Bertini.FamilyDivisors.exists_mem_and_sectionOf_ne_zero`: a nonempty open of the
  parameter space `𝔸^r_k` contains a `k`-rational point whose vector is outside `ker ψ`. This is
  what makes the conclusion a statement about an honest hyperplane section.
* `Stacks.Bertini.FamilyDivisors.isAmple_of_isImmersive`: `L = 𝒪_X(1)` is ample, from the closed
  immersion of `X` into the projective space of the linear system.

## The proof

It is the remark's own three-step argument.

1. **Smoothness, from [Stacks, Tag 0FD6]**
   (`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor`): hypotheses (1), (2)
   and (3) give one nonempty open `U ⊂ 𝔸^r_k` over whose field-valued points the divisor is
   smooth.
2. **Connectedness, by Enriques–Severi–Zariski** ([Stacks, Tag 0FD9], available as
   `Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple`), applied to `X` and the
   section `ψ(v)`. Its three hypotheses are discharged here: `ψ(v)` is a regular section because
   it is nonzero on an integral scheme (`AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero`);
   `depth(𝒪_{X,x}) ≥ 2` at every closed point because `X` is smooth, hence regular and so normal
   and locally Noetherian, and `dim 𝒪_{X,x} ≥ 2`
   (`AlgebraicGeometry.two_le_depth_stalk_of_two_le_coheight`, Serre's criterion); and `X` is
   connected because it is irreducible.
3. **Smooth and connected gives irreducible**: a connected scheme smooth over a field is
   integral (`Stacks.Chow.isIntegral_of_connectedSpace_of_smooth`, [Stacks, Tag 056S] and
   [Stacks, Tag 033N]), hence irreducible.

The two conclusions are about two presentations of the same scheme and have to be matched. Step 1
concludes about `H_v ⊂ X_k`, the base change of `X` along the identity of `k`; step 2 concludes
about `Z(ψ(v)) ⊂ X`. They agree because `H_v` is the inverse image of `Z(ψ(v))` along the
projection `X_k → X` (`Stacks.Bertini.FamilyDivisors.specializedDivisor_self_eq_comap`), which is
an isomorphism (`Stacks.Bertini.FamilyDivisors.isIso_baseChangeToX` at a bijective extension of
the base field); the comparison of closed subschemes is then
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` composed with the projection of the fibre
product, both isomorphisms.

## Implementation notes

The remark says "for a general `v`" and then uses one `v`; producing it is where the hypothesis
that `k` be algebraically closed enters, and it enters twice. Once to get a `k`-rational point of
the open `U`: an algebraically closed field is infinite, so
`Stacks.Bertini.FamilyDivisors.exists_parameterPoint_mem` applies. And once more implicitly,
since over a non-closed field the open produced by [Stacks, Tag 0FD6] need not have a rational
point at all.

The side condition `ψ(v) ≠ 0` is not decoration: it is what [Stacks, Tag 0FD9] needs to see
`ψ(v)` as a regular section, and it is what makes `H_v` a hyperplane *section* rather than all of
`X`. It is arranged by shrinking `U`. Generation gives a vector `v₀` with `ψ(v₀) ≠ 0`, so
`ker ψ < V`; a linear functional `χ` on `V` vanishing on `ker ψ` with `χ(v₀) ≠ 0`
(`Submodule.exists_dual_map_eq_bot_of_notMem`) has `χ ≠ 0`, so the linear form
`∑ᵢ χ(vᵢ) xᵢ` is a nonzero polynomial on `𝔸^r_k`, its basic open is nonempty because `𝔸^r_k` is
reduced, and that open meets `U` because `𝔸^r_k` is irreducible. A rational point of the
intersection has `χ(v) ≠ 0`, hence `v ∉ ker ψ`.

The dimension hypothesis of the tag is the source's `dim X ≥ 2`, as
`2 ≤ topologicalKrullDim X`. [Stacks, Tag 0FD9] consumes it at the closed points, as
`2 ≤ coheight x`, which by [Stacks, Tag 02IZ] is `2 ≤ dim 𝒪_{X,x}`; the passage is
`Stacks.Bertini.FamilyDivisors.two_le_coheight_of_two_le_topologicalKrullDim`: an irreducible
scheme locally of finite type over a field has local dimension `dim X` at every point, and at a
closed point that is `dim 𝒪_{X,x}` ([Stacks, Tag 0A21]).

## References

* [Stacks Project, Tag 0G4G](https://stacks.math.columbia.edu/tag/0G4G)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-! ### The linear system does not vanish identically -/

/-- **The linear system does not vanish identically** when it generates `L` and `X` is
nonempty: at a point of `X` some `ψ(v)` has a germ outside `𝔪ₓ · Lₓ`, and the germ of the zero
section lies in `𝔪ₓ · Lₓ`. -/
theorem exists_sectionOf_ne_zero (h : D.Generates) (x : D.X) : ∃ v : D.V, D.sectionOf v ≠ 0 := by
  obtain ⟨v, hv⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks
    D.sectionOf h x
  rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff] at hv
  refine ⟨v, fun h0 => hv ?_⟩
  rw [h0, map_zero]
  exact Submodule.zero_mem _

/-- **The linear system is nonzero**, so `dim V ≥ 1`: a vector with `ψ(v) ≠ 0` is nonzero. -/
theorem finrank_pos_of_generates (h : D.Generates) (x : D.X) : 0 < Module.finrank D.k D.V := by
  obtain ⟨v₀, hv₀⟩ := D.exists_sectionOf_ne_zero h x
  have hψ : D.ψ v₀ ≠ 0 := hv₀
  refine Module.finrank_pos_iff.mpr ⟨v₀, 0, fun h0 => hψ ?_⟩
  rw [h0, map_zero]

/-! ### `L` is ample -/

/-- **`L = 𝒪_X(1)` is ample**, when `X` is proper over `k` and the morphism `φ_{L,ψ}` to the
projective space of the linear system is an immersion — that is, when `X ⊂ 𝐏^n_k` is a closed
subscheme and `L` is its hyperplane class.

`φ` is proper over `k` because `X` is and `𝐏^n_k` is separated ([Stacks, Tag 01W6]), so its
image is closed; an immersion with closed image is a closed immersion. The hyperplane sheaf of
`𝐏^n_k` is ample over the affine base `Spec k`
(`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`), its restriction to a closed
subscheme is ample ([Stacks, Tag 01PU]), and `φ^* 𝒪(1) ≅ L`
(`AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver`). -/
theorem isAmple_of_isImmersive [IsProper D.toBase] (hgen : D.Generates) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) D.k D.V)
    (himm : D.IsImmersive b (D.generatesBy_basis hgen b)) :
    AlgebraicGeometry.Scheme.Modules.IsAmple D.X D.L := by
  set s : Fin (n + 1) → Γ(D.L, ⊤) := fun i => D.sectionOf (b i)
  have hgs : Stacks.ProjectiveFromSections.GeneratesStalks s := D.generatesBy_basis hgen b
  have : IsImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hgs D.toBase) :=
    (D.isImmersive_iff_isImmersion_toProjectiveSpaceOver b
      (D.generatesBy_basis hgen b)).mp himm
  set φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hgs D.toBase
  have : IsProper (projectiveSpaceOver n (Spec (.of D.k)) ↘ Spec (.of D.k)) :=
    isProper_projectiveSpaceOver n (Spec (.of D.k))
  have hover : φ ≫ (projectiveSpaceOver n (Spec (.of D.k)) ↘ Spec (.of D.k)) = D.toBase :=
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst s hgs D.toBase
  have hclosed : IsClosed (Set.range (φ.base)) :=
    AlgebraicGeometry.isClosed_range_of_universallyClosed_of_isSeparated φ
      (projectiveSpaceOver n (Spec (.of D.k)) ↘ Spec (.of D.k)) D.toBase hover
  have : IsClosedImmersion φ := IsClosedImmersion.of_isPreimmersion φ hclosed
  have hPample : AlgebraicGeometry.Scheme.Modules.IsAmple (projectiveSpaceOver n (Spec (.of D.k)))
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of D.k))) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).1
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n (Spec (.of D.k)))
  have hpull := AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isClosedImmersion
    φ (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of D.k))) hPample
  obtain ⟨θ, -⟩ :=
    AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver s hgs D.toBase
  exact AlgebraicGeometry.Scheme.Modules.isAmple_of_iso θ hpull

/-- `L` is ample when the linear system generates `L` and all its `φ_{L,ψ}` are immersions. -/
private theorem isAmple_of_forall_isImmersive [IsProper D.toBase] (hgen : D.Generates) (x : D.X)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b)) :
    AlgebraicGeometry.Scheme.Modules.IsAmple D.X D.L := by
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank D.k D.V = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (D.finrank_pos_of_generates hgen x)).symm⟩
  exact D.isAmple_of_isImmersive hgen (D.basis.reindex (finCongr hm)) (himm m _)

/-- A connected scheme smooth over a field is irreducible. -/
private theorem irreducibleSpace_of_smooth_of_connectedSpace {k : Type u} [Field k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [Smooth p] [ConnectedSpace Y] : IrreducibleSpace Y := by
  have := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth p
  infer_instance

/-! ### A rational member that is not identically zero -/

/-- **A nonempty open of `𝔸^r_k` contains a rational point whose vector is outside `ker ψ`**,
when `k` is infinite and the linear system generates `L` on a nonempty `X`.

A functional `χ` on `V` vanishing on `ker ψ` and not on a vector with `ψ(v₀) ≠ 0` gives the
nonzero linear form `∑ᵢ χ(vᵢ) xᵢ` on `𝔸^r_k`; its basic open is nonempty because `𝔸^r_k` is
reduced, meets `U` because `𝔸^r_k` is irreducible, and a rational point of the intersection has
`χ(v) ≠ 0`, so `v ∉ ker ψ`. -/
theorem exists_mem_and_sectionOf_ne_zero [Infinite D.k] (h : D.Generates) (x : D.X)
    (U : D.parameterBase.Opens) (hU : (U : Set D.parameterBase).Nonempty) :
    ∃ c : Fin (Module.finrank D.k D.V) → D.k,
      (∀ p : Spec (.of D.k), D.parameterPoint c p ∈ U) ∧
        D.sectionOf (∑ i, c i • D.basis i) ≠ 0 := by
  classical
  obtain ⟨v₀, hv₀⟩ := D.exists_sectionOf_ne_zero h x
  have hψ : D.ψ v₀ ≠ 0 := hv₀
  obtain ⟨χ, hχ₀, hχker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := LinearMap.ker D.ψ) hψ inferInstance
  -- the linear form `∑ᵢ χ(vᵢ) xᵢ`, as a polynomial function on `𝔸^r_k`
  set G : MvPolynomial D.basisIndex D.k :=
    ∑ i, MvPolynomial.C (χ (D.basis i)) * MvPolynomial.X (ULift.up i) with hGdef
  have hGeval : ∀ c : Fin (Module.finrank D.k D.V) → D.k,
      MvPolynomial.eval (fun j => c j.down) G = χ (∑ i, c i • D.basis i) := by
    intro c
    rw [hGdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hG : G ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, χ (D.basis i) ≠ 0 := by
      by_contra hc
      have hzero : χ = 0 :=
        D.basis.ext fun i => by simpa using not_not.mp (not_exists.mp hc i)
      exact hχ₀ (by rw [hzero]; simp)
    intro h0
    refine hi₀ ?_
    have hev := congrArg
      (MvPolynomial.eval (fun j => if j = ULift.up i₀ then (1 : D.k) else 0)) h0
    rw [map_zero, hGdef, map_sum] at hev
    rw [← hev, Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; simp [MvPolynomial.eval_X, ULift.up_injective.ne hj]
    · simp
  -- the basic open of a nonzero polynomial is nonempty
  have hWne : ((D.parameterBase.basicOpen (D.parameterBaseΓEquiv G) :
      D.parameterBase.Opens) : Set D.parameterBase).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hbot : D.parameterBase.basicOpen (D.parameterBaseΓEquiv G) = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hy
      exact (hempty ▸ hy : y ∈ (∅ : Set D.parameterBase))
    exact hG (D.parameterBaseΓEquiv.injective
      (by rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hbot; rw [hbot, map_zero]))
  -- it meets `U` because `𝔸^r_k` is irreducible
  have := D.irreducibleSpace_parameterBase
  have hinter : ((U ⊓ D.parameterBase.basicOpen (D.parameterBaseΓEquiv G) :
      D.parameterBase.Opens) : Set D.parameterBase).Nonempty := by
    have hirr := (IrreducibleSpace.isIrreducible_univ D.parameterBase).2 U
      (D.parameterBase.basicOpen (D.parameterBaseΓEquiv G)) U.2
      (D.parameterBase.basicOpen (D.parameterBaseΓEquiv G)).2 (by simpa using hU)
      (by simpa using hWne)
    simpa using hirr
  obtain ⟨c, -, hc⟩ := D.exists_parameterPoint_mem (D.finrank_pos_of_generates h x) _ hinter
  refine ⟨c, fun p => (hc p).1, fun h0 => ?_⟩
  -- the rational point lies in the basic open, so `χ(v) ≠ 0`, so `v ∉ ker ψ`
  obtain ⟨p⟩ : Nonempty (Spec (.of D.k)) := ⟨IsLocalRing.closedPoint D.k⟩
  have hp : p ∈ (D.parameterPoint c) ⁻¹ᵁ
      D.parameterBase.basicOpen (D.parameterBaseΓEquiv G) := (hc p).2
  have hzero : MvPolynomial.eval (fun j => c j.down) G = 0 := by
    rw [hGeval c]
    have hmem : (∑ i, c i • D.basis i) ∈ LinearMap.ker D.ψ := h0
    have : χ (∑ i, c i • D.basis i) ∈ (LinearMap.ker D.ψ).map χ :=
      Submodule.mem_map_of_mem hmem
    rwa [hχker, Submodule.mem_bot] at this
  rw [Scheme.preimage_basicOpen_top, D.parameterPoint_appTop_parameterBaseΓEquiv c G, hzero,
    map_zero, Scheme.basicOpen_zero] at hp
  exact hp

/-! ### Enriques–Severi–Zariski on `X` -/

/-- **[Stacks, Tag 0FD9] applied to `X` and a nonzero member of the linear system.** If `X` is
proper over `k`, smooth, connected, irreducible, with `dim 𝒪_{X,x} ≥ 2` at every closed point,
and `L` is ample, then the divisor `H_v` of a vector with `ψ(v) ≠ 0` is connected. -/
theorem connectedSpace_divisor [Smooth D.toBase] [IsProper D.toBase] [ConnectedSpace D.X]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple D.X D.L)
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) → (2 : ℕ∞) ≤ Order.coheight x)
    (v : D.V) (hv : D.sectionOf v ≠ 0) :
    ConnectedSpace (D.divisor v).subscheme := by
  have : AlgebraicGeometry.IsIntegral D.X :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth D.toBase
  have hreg : IsRegular D.X := isRegular_of_smooth_over_field D.toBase
  let : IsLocallyNoetherian D.X := isLocallyNoetherian_of_isRegular hreg
  let : IsNormal D.X := isNormal_of_isRegular D.X hreg
  have hdepth : ∀ x : D.X, IsClosed ({x} : Set D.X) → (2 : ℕ∞) ≤
      Module.depth (D.X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (D.X.presheaf.stalk x)) (D.X.presheaf.stalk x) :=
    fun x hx => AlgebraicGeometry.two_le_depth_stalk_of_two_le_coheight x (hdim x hx)
  have heq : (Stacks.SheafOfModules.sectionsOfTop D.L (D.sectionOf v)).eval (op ⊤) =
      D.sectionOf v :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top D.L (D.sectionOf v)
  have hreg' : IsRegularSection D.X.sheaf.obj D.X.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop D.L (D.sectionOf v)) :=
    AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero D.L _ fun hz => hv (heq ▸ hz)
  have hcon := Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple D.k D.toBase
    D.L hample (Stacks.SheafOfModules.sectionsOfTop D.L (D.sectionOf v)) hreg' hdepth
  show ConnectedSpace (zeroScheme D.X D.L (D.sectionOf v)).subscheme
  exact heq ▸ hcon

/-- The projection of `X_k ×_X I` to `I` is an isomorphism, as `X_k → X` is. -/
private theorem isIso_pullback_snd_baseChangeToX (I : D.X.IdealSheafData) :
    IsIso (pullback.snd (D.baseChangeToX D.k) I.subschemeι) :=
  have := D.isIso_baseChangeToX D.k Function.bijective_id
  (IsPullback.of_hasPullback (D.baseChangeToX D.k) I.subschemeι).isIso_snd_of_isIso

/-- **`H_v ⊂ X_k` and `Z(ψ(v)) ⊂ X` are the same scheme.** Over the base field itself the
divisor of a coordinate tuple is the inverse image of the divisor of its vector along the
projection `X_k → X`, which is an isomorphism; so connectedness of one is connectedness of the
other. -/
theorem connectedSpace_specializedDivisor_of_connectedSpace_divisor
    (c : Fin (Module.finrank D.k D.V) → D.k)
    (h : ConnectedSpace (D.divisor (∑ i, c i • D.basis i)).subscheme) :
    ConnectedSpace (D.specializedDivisor D.k c).subscheme := by
  rw [D.specializedDivisor_self_eq_comap c]
  set I := D.divisor (∑ i, c i • D.basis i)
  have := D.isIso_pullback_snd_baseChangeToX I
  exact (Scheme.homeoOfIso (I.comapIso (D.baseChangeToX D.k) ≪≫
    asIso (pullback.snd (D.baseChangeToX D.k) I.subschemeι))).connectedSpace_iff.mpr h

/-! ### The dimension hypothesis, read at the closed points -/

/-- **`dim X ≥ 2` gives `dim 𝒪_{X,x} ≥ 2` at every closed point** of an irreducible `X` smooth
over `k`. An irreducible scheme locally of finite type over a field has dimension `dim X` at
every point ([Stacks, Tag 0A21],
`AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible`), the local
dimension at a closed point is `dim 𝒪_{X,x}`
(`AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk`), and that is the coheight
of `x` ([Stacks, Tag 02IZ]). -/
theorem two_le_coheight_of_two_le_topologicalKrullDim [Smooth D.toBase] [IrreducibleSpace D.X]
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim D.X) (x : D.X)
    (hx : IsClosed ({x} : Set D.X)) : (2 : ℕ∞) ≤ Order.coheight x := by
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible D.k D.X D.toBase x,
    topologicalKrullDimAt_eq_krullDimOfRing_stalk D.k D.X D.toBase x hx,
    ringKrullDim_stalk_eq_coheight] at hdim
  exact WithBot.coe_le_coe.mp hdim

/-! ### The claim with the dimension read at the closed points -/

/-- **The claim of [Stacks, Tag 0G4G] with `dim X ≥ 2` read at the closed points**, as
`2 ≤ coheight x` for every closed point `x`; this is the form [Stacks, Tag 0FD9] consumes. The
tag itself, with the source's `dim X ≥ 2`, is
`Stacks.Bertini.FamilyDivisors.exists_smooth_irreducibleSpace_specializedDivisor`. -/
theorem exists_smooth_irreducibleSpace_specializedDivisor_of_coheight [IsAlgClosed D.k]
    [Smooth D.toBase] [IsProper D.toBase] [IrreducibleSpace D.X] (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) → (2 : ℕ∞) ≤ Order.coheight x) :
    ∃ c : Fin (Module.finrank D.k D.V) → D.k,
      D.sectionOf (∑ i, c i • D.basis i) ≠ 0 ∧
        Smooth ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k) ∧
          IrreducibleSpace (D.specializedDivisor D.k c).subscheme := by
  -- Step 1: the open of parameters with smooth divisor, from Tag 0FD6
  obtain ⟨U, hUne, hU⟩ := D.forGeneral_smooth_specializedDivisor hgen himm
  -- a rational point of it whose vector is not in `ker ψ`
  obtain ⟨c, hcU, hcne⟩ := D.exists_mem_and_sectionOf_ne_zero hgen
    (Classical.arbitrary D.X) U hUne
  have hsmooth : Smooth ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k) :=
    hU D.k c hcU c rfl
  refine ⟨c, hcne, hsmooth, ?_⟩
  -- `L` is ample because `X` is a closed subscheme of the projective space of the system
  have hample := D.isAmple_of_forall_isImmersive hgen (Classical.arbitrary D.X) himm
  -- Step 2: connectedness, by Enriques-Severi-Zariski
  have : ConnectedSpace (D.specializedDivisor D.k c).subscheme :=
    D.connectedSpace_specializedDivisor_of_connectedSpace_divisor c
      (D.connectedSpace_divisor hample hdim _ hcne)
  -- Step 3: smooth and connected gives irreducible
  exact irreducibleSpace_of_smooth_of_connectedSpace
    ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k)

/-! ### The tag -/

/-- **[Stacks, Tag 0G4G] for an arbitrary linear system.** Let `k` be an algebraically closed
field and let `X ⊂ 𝐏^n_k` be smooth and irreducible of dimension `≥ 2`. Then there is a
hyperplane `H ⊂ 𝐏^n_k` such that `X ∩ H` is smooth and irreducible. The tag as the source states
it, for a closed subscheme of `ℙⁿ_k`, is
`Stacks.Bertini.ProjectiveSubscheme.exists_hyperplane_smooth_irreducibleSpace`.

The remark works in the standing situation of [Stacks, Tag 0G47] with
`V = k T_0 ⊕ … ⊕ k T_n`, `L = 𝒪_X(1)` and `ψ` the restriction of the coordinates to `X`; the
hyperplane attached to `v ∈ V` is `H_v` and `X ∩ H_v` is the divisor `Z(ψ(v))`, which over `k`
itself is `Stacks.Bertini.FamilyDivisors.specializedDivisor` at the coordinate tuple of `v`.
The inclusion `X ⊂ 𝐏^n_k` is read as the remark reads it when it invokes
[Stacks, Tag 0FD6]: `ψ` generates `L` (hypothesis (2) there) and the morphism
`φ_{L,ψ} : X → 𝐏(V)` it determines is an immersion (hypothesis (3) there, at every basis,
equivalently at one by `Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'`), together with
properness of `X` over `k`, which says that the immersion is a closed one. This is a
generalization: `V` may be any finite dimensional linear system, `ψ` need not be injective.
Nothing else about the embedding is assumed: ampleness of `L`, which Enriques–Severi–Zariski
needs, is derived by `Stacks.Bertini.FamilyDivisors.isAmple_of_isImmersive`. "Of dimension
`≥ 2`" is `2 ≤ dim X`, the Krull dimension of the underlying space.

The conclusion asserts in addition `ψ(v) ≠ 0`, that is `X ⊄ H_v`: the hyperplane is honest and
`X ∩ H_v` is a genuine hyperplane section, not the whole of `X`.

The proof is the remark's: smoothness of the general member is [Stacks, Tag 0FD6],
connectedness is Enriques–Severi–Zariski in the form [Stacks, Tag 0FD9], and a connected scheme
smooth over a field is irreducible. -/
@[stacks 0G4G "for an arbitrary finite dimensional linear system with phi_(L, psi) a closed \
immersion: the hyperplane section is H_v over k itself"]
theorem exists_smooth_irreducibleSpace_specializedDivisor [IsAlgClosed D.k] [Smooth D.toBase]
    [IsProper D.toBase] [IrreducibleSpace D.X] (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim D.X) :
    ∃ c : Fin (Module.finrank D.k D.V) → D.k,
      D.sectionOf (∑ i, c i • D.basis i) ≠ 0 ∧
        Smooth ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k) ∧
          IrreducibleSpace (D.specializedDivisor D.k c).subscheme :=
  D.exists_smooth_irreducibleSpace_specializedDivisor_of_coheight hgen himm
    (D.two_le_coheight_of_two_le_topologicalKrullDim hdim)

/-! ### The claim on `X` itself -/

/-- **Smoothness of `H_v ⊂ X_k` is smoothness of `Z(ψ(v)) ⊂ X`.** Over the base field itself
`H_v` is the inverse image of `Z(ψ(v))` along the projection `X_k → X`, an isomorphism lying over
`Spec k`, so the two closed subschemes are isomorphic over `Spec k`. -/
theorem smooth_divisor_of_smooth_specializedDivisor (c : Fin (Module.finrank D.k D.V) → D.k)
    (h : Smooth ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k)) :
    Smooth ((D.divisor (∑ i, c i • D.basis i)).subschemeι ≫ D.toBase) := by
  set I := D.divisor (∑ i, c i • D.basis i)
  have := D.isIso_pullback_snd_baseChangeToX I
  let e : (I.comap (D.baseChangeToX D.k)).subscheme ≅ I.subscheme :=
    I.comapIso (D.baseChangeToX D.k) ≪≫ asIso (pullback.snd (D.baseChangeToX D.k) I.subschemeι)
  have hπ : D.baseChangeToX D.k ≫ D.toBase = D.baseChangeToSpec D.k := by
    rw [(D.isPullback_baseChange D.k).w]
    simp
  have he : I.subschemeι ≫ D.toBase =
      e.inv ≫ (I.comap (D.baseChangeToX D.k)).subschemeι ≫ D.baseChangeToSpec D.k := by
    rw [← hπ, Iso.eq_inv_comp]
    simp only [e, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [D.specializedDivisor_self_eq_comap c] at h
  rw [he]
  infer_instance

/-- **[Stacks, Tag 0G4G] stated on `X` itself**: in the standing situation, with the hypotheses
of the tag, some `v ∈ V` has `ψ(v) ≠ 0` and `Z(ψ(v)) ⊂ X` smooth over `k` and irreducible. -/
theorem exists_smooth_irreducibleSpace_divisor [IsAlgClosed D.k] [Smooth D.toBase]
    [IsProper D.toBase] [IrreducibleSpace D.X] (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim D.X) :
    ∃ v : D.V, D.sectionOf v ≠ 0 ∧ Smooth ((D.divisor v).subschemeι ≫ D.toBase) ∧
      IrreducibleSpace (D.divisor v).subscheme := by
  obtain ⟨U, hUne, hU⟩ := D.forGeneral_smooth_specializedDivisor hgen himm
  obtain ⟨c, hcU, hcne⟩ := D.exists_mem_and_sectionOf_ne_zero hgen
    (Classical.arbitrary D.X) U hUne
  have hsmooth : Smooth ((D.divisor (∑ i, c i • D.basis i)).subschemeι ≫ D.toBase) :=
    D.smooth_divisor_of_smooth_specializedDivisor c (hU D.k c hcU c rfl)
  refine ⟨_, hcne, hsmooth, ?_⟩
  have hample := D.isAmple_of_forall_isImmersive hgen (Classical.arbitrary D.X) himm
  have : ConnectedSpace (D.divisor (∑ i, c i • D.basis i)).subscheme :=
    D.connectedSpace_divisor hample (D.two_le_coheight_of_two_le_topologicalKrullDim hdim) _ hcne
  exact irreducibleSpace_of_smooth_of_connectedSpace
    ((D.divisor (∑ i, c i • D.basis i)).subschemeι ≫ D.toBase)

end Stacks.Bertini.FamilyDivisors

/-! ### A closed subscheme of `ℙⁿ_k` and its hyperplane sections -/

namespace Stacks.Bertini.ProjectiveSubscheme

open Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion

variable {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}
  (i : X ⟶ projectiveSpaceOver n (Spec (.of k)))

/-- **The standing situation of [Stacks, Tag 0G47] attached to `X ⊂ ℙⁿ_k`**, as in the remark:
`V = k T_0 ⊕ … ⊕ k T_n` is `kⁿ⁺¹`, `L = 𝒪_X(1)` is the pullback of the hyperplane sheaf along
`X → ℙⁿ_k → ℙⁿ_ℤ`, and `ψ` sends the `j`-th standard vector to the restriction `T_j|_X` of the
`j`-th homogeneous coordinate. -/
abbrev family : FamilyDivisors.{u, u} where
  k := k
  V := Fin (n + 1) → k
  X := X
  toBase := i ≫ pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse.{u} n))
  L := (Scheme.Modules.pullback
    (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n)
  isInvertible := Stacks.TwistPullbackPinned.isInvertibleModule_pullback_twistingSheafAtUniverse _
  ψ := Fintype.linearCombination k (M := globalSections k
      (i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      ((Scheme.Modules.pullback
        (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} n)))
    (Stacks.TwistPullbackPinned.pullbackCoordSection
      (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))))
  basis := (Pi.basisFun k (Fin (n + 1))).reindex (finCongr (Module.finrank_fin_fun k).symm)

/-- `ψ` sends the `j`-th standard vector to `T_j|_X`. -/
theorem family_sectionOf_single (j : Fin (n + 1)) :
    (family i).sectionOf (Pi.single j 1) =
      Stacks.TwistPullbackPinned.pullbackCoordSection
        (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) j := by
  classical
  have h := Fintype.linearCombination_apply_single (R := k)
    (M := globalSections k (family i).toBase (family i).L)
    (Stacks.TwistPullbackPinned.pullbackCoordSection
      (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))) j (1 : k)
  exact h.trans (one_smul k _)

/-- **Hypothesis (2) of [Stacks, Tag 0FD6] for `X ⊂ ℙⁿ_k`**: the restrictions of the
coordinates generate `𝒪_X(1)` ([Stacks, Tag 01NE],
`Stacks.ProjectiveSpaceModuli.taut_generates`). -/
theorem family_generates : (family i).Generates := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks _
    (Stacks.ProjectiveSpaceModuli.taut_generates
      (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))) x
  refine ⟨Pi.single j 1, ?_⟩
  show x ∈ nvOpen _ ((family i).sectionOf (Pi.single j 1))
  rw [family_sectionOf_single]
  exact hj

/-- **The morphism of [Stacks, Tag 01ND] attached to the restricted coordinates is the inclusion
`X → ℙⁿ_k` itself**: both are pinned by the same family on the charts `X_{T_j}`, and a pinned
morphism is unique (`Stacks.VeryAmpleGlue.eq_of_pin_pullbackCoordSection`). -/
theorem toProjectiveSpaceOver_eq_of_eq
    (s : Fin (n + 1) → Γ((family i).L, ⊤)) (hs : GeneratesStalks s)
    (h : s = Stacks.TwistPullbackPinned.pullbackCoordSection
      (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))) :
    toProjectiveSpaceOver s hs (family i).toBase = i := by
  subst h
  exact Stacks.VeryAmpleGlue.eq_of_pin_pullbackCoordSection _ i _ rfl
    (toProjectiveSpaceOver_fst _ _ _) fun j => ι_toProjectiveSpaceOver _ _ _ j

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] for `X ⊂ ℙⁿ_k`**, at every basis of `V`: the morphism
`φ_{L,ψ}` is the inclusion at the standard basis, and the hypothesis does not depend on the
basis (`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'`). -/
theorem family_isImmersive [IsImmersion i] (m : ℕ)
    (b : Module.Basis (Fin (m + 1)) (family i).k (family i).V) :
    (family i).IsImmersive b ((family i).generatesBy_basis (family_generates i) b) := by
  have key : ∀ (s : Fin (n + 1) → Γ((family i).L, ⊤)) (hs : GeneratesStalks s),
      s = Stacks.TwistPullbackPinned.pullbackCoordSection
        (i ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) →
      IsImmersion (toProjectiveSpaceOver s hs (family i).toBase) := by
    intro s hs hseq
    rw [toProjectiveSpaceOver_eq_of_eq i s hs hseq]
    infer_instance
  have h0 : (family i).IsImmersive (Pi.basisFun k (Fin (n + 1)))
      ((family i).generatesBy_basis (family_generates i) _) :=
    ((family i).isImmersive_iff_isImmersion_toProjectiveSpaceOver _ _).mpr
      (key _ _ (funext fun j => by
        rw [Pi.basisFun_apply]
        exact family_sectionOf_single i j))
  exact ((family i).isImmersive_congr_basis' _ b _ _).mp h0

/-- **`X ∩ H = Z(ψ(c))`**: the inverse image in `X` of the hyperplane `H = Z(∑ⱼ cⱼ Tⱼ) ⊂ ℙⁿ_k` is
the divisor of the vector `c` of the linear system ([Stacks, Tag 0B6Y], through
`Stacks.Bertini.zeroScheme_sum_smul_comap`). -/
theorem comap_hyperplane (c : Fin (n + 1) → k) :
    (Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.hyperplane n (Spec (.of k))
      (Stacks.Divisors.sectionsOfTop (projectiveSpaceTwistingSheaf n (Spec (.of k)))
        (∑ j, (pullback.fst (terminal.from (Spec (.of k)))
            (terminal.from (projectiveSpaceAtUniverse.{u} n))).appTop
              ((Scheme.ΓSpecIso (.of k)).inv (c j)) •
          pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
            (twistingSheafAtUniverse.{u} n)
            (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n j)))).comap i =
      (family i).divisor c := by
  rw [show ∀ s, Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.hyperplane n
      (Spec (.of k)) s = zeroScheme _ (projectiveSpaceTwistingSheaf n (Spec (.of k)))
        (s.eval (op ⊤)) from fun _ => rfl,
    Stacks.Divisors.sectionsOfTop_eval_top]
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (projectiveSpaceAtUniverse.{u} n).sheaf.obj
      (projectiveSpaceAtUniverse.{u} n).ringCatSheaf.property (twistingSheafAtUniverse.{u} n) :=
    Stacks.TwistInvertibleOverBase.isInvertibleModule_twistingSheafAtUniverse n
  exact (zeroScheme_sum_smul_comap (twistingSheafAtUniverse.{u} n)
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i _ rfl _
    (fun j => (family i).baseScalar (c j)) (fun j => rfl)
    (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n)).symm

/-- **[Stacks, Tag 0G4G].** Let `k` be an algebraically closed field and let `X ⊂ 𝐏^n_k` be
smooth and irreducible of dimension `≥ 2`. Then there is a hyperplane `H ⊂ 𝐏^n_k` such that
`X ∩ H` is smooth and irreducible.

`X ⊂ 𝐏^n_k` is a closed immersion `i : X → ℙⁿ_k`, and `X` is smooth over `k` through it. A
hyperplane is `H = Z(∑ⱼ cⱼ Tⱼ)` for a nonzero `c ∈ kⁿ⁺¹`, the zero scheme of a nonzero linear
form in the homogeneous coordinates `T_0, …, T_n` of `𝒪(1)`
(`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.hyperplane`), and `X ∩ H` is its
scheme-theoretic inverse image `H.comap i`. "Of dimension `≥ 2`" is `2 ≤ dim X`.

The proof is the remark's: smoothness of the general hyperplane section is [Stacks, Tag 0FD6],
connectedness is Enriques–Severi–Zariski in the form [Stacks, Tag 0FD9], and a connected scheme
smooth over a field is irreducible
(`Stacks.Bertini.FamilyDivisors.exists_smooth_irreducibleSpace_divisor`, applied to the standing
situation `Stacks.Bertini.ProjectiveSubscheme.family` of the remark). -/
@[stacks 0G4G]
theorem exists_hyperplane_smooth_irreducibleSpace [IsAlgClosed k] [IsClosedImmersion i]
    [Smooth (i ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)))]
    [IrreducibleSpace X] (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ c : Fin (n + 1) → k, c ≠ 0 ∧
      let H := Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.hyperplane n
        (Spec (.of k))
        (Stacks.Divisors.sectionsOfTop (projectiveSpaceTwistingSheaf n (Spec (.of k)))
          (∑ j, (pullback.fst (terminal.from (Spec (.of k)))
              (terminal.from (projectiveSpaceAtUniverse.{u} n))).appTop
                ((Scheme.ΓSpecIso (.of k)).inv (c j)) •
            pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
              (twistingSheafAtUniverse.{u} n)
              (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n j)))
      Smooth ((H.comap i).subschemeι ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n))) ∧
        IrreducibleSpace (H.comap i).subscheme := by
  have : IsProper (family i).toBase := by
    have : IsProper (pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
      isProper_projectiveSpaceOver n (Spec (.of k))
    show IsProper (i ≫ _)
    infer_instance
  obtain ⟨c, hc, hsm, hirr⟩ := (family i).exists_smooth_irreducibleSpace_divisor
    (family_generates i) (family_isImmersive i) hdim
  refine ⟨c, fun h0 => hc (by rw [h0]; exact (family i).sectionOf_zero), ?_⟩
  intro H
  have hH : H.comap i = (family i).divisor c := comap_hyperplane i c
  refine ⟨?_, ?_⟩
  · rw [hH]
    exact hsm
  · rw [hH]
    exact hirr

end Stacks.Bertini.ProjectiveSubscheme

end
