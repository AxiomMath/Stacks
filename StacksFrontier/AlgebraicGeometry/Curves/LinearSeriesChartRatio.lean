module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical

/-!
# The charts and the chart ratios of the morphism attached to a family of sections

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s₀, …, sₙ` global sections of `L`
generating every stalk, so that [Stacks, Tag 01ND] attaches to them a morphism
`φ = φ_{(L, (s₀, …, sₙ))} : X ⟶ 𝐏ⁿ_ℤ`
(`Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse`). This file relates the two
descriptions of the `i`-th chart of `φ`:

* the nonvanishing open `X_{sᵢ}`, which is where the ratios `s_k / sᵢ` live;
* the inverse image `φ⁻¹(D₊(Tᵢ))` of the `i`-th standard open of projective space, which is
  where the degree-zero fractions `T_j / Tᵢ` can be pulled back.

They are the *same* open, and under that identification the ratio `s_j / sᵢ` is the pullback of
`T_j / Tᵢ`. Consequently the germ of `s_j / sᵢ` at a point of `X_{sᵢ}` lies in the image of the
stalk map of `φ`: the chart ratios of `φ` are functions pulled back from projective space.

Two further facts about nonvanishing opens are proved along the way. At the generic point of an
integral scheme the local ring is a field, so `𝔪_x · L_x` is the zero submodule and a section
fails to vanish exactly when its germ is nonzero. And ratios are insensitive to a morphism of
invertible modules carrying one family of sections to another, because a ratio is characterised
by the equation it solves and a morphism of modules is semilinear.

## Main results

* `Stacks.ProjectiveFromSections.maximalSmul_genericPoint_eq_bot` and
  `Stacks.ProjectiveFromSections.mem_nvOpen_genericPoint_of_germ_ne_zero`: **the generic point of
  an integral scheme lies in `X_u` as soon as the germ of `u` there is nonzero.**
* `Stacks.ProjectiveFromSections.germ_ratio_eq_of_app_eq`: **ratios agree under a morphism of
  modules matching the two families of sections**, after taking germs at a point of both charts.
* `Stacks.ProjectiveFromSections.germ_ratio_mem_range_stalkMap`: **the germ of `s_j / sᵢ` is in
  the range of the stalk map of `φ`**, the witness being the germ of `T_j / Tᵢ`.
* `Stacks.ProjectiveFromSections.preimage_basicOpen_eq_nvCover_canonical` and
  `Stacks.ProjectiveFromSections.preimage_basicOpen_le_nvCover_canonical`: **`φ⁻¹(D₊(Tᵢ))` is
  `X_{sᵢ}`**, the inclusion converse to
  `Stacks.TwistPullbackPinned.nvCover_le_preimage_basicOpen` and the resulting equality.

## Implementation notes

The chart identification is the one place where the twist comparison is consumed. The inclusion
`X_{sᵢ} ⊆ φ⁻¹(D₊(Tᵢ))` is read off the pinning of `φ` and is already proved; the converse needs
to know that `X_{sᵢ}` is *all* of `φ⁻¹(D₊(Tᵢ))`, and the only description of the latter as a
nonvanishing open is `Stacks.ProjectiveSpaceModuli.nvOpen_pullbackCoordSection`, in the pulled
back module `φ^* 𝒪(1)` and for the pulled back coordinate `φ^* Tᵢ`. So the isomorphism
`φ^* 𝒪(1) ≅ L` carrying `φ^* Tᵢ` to `sᵢ` is what closes the gap, and that is
`AlgebraicGeometry.exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse`. The transport
itself costs nothing: `Stacks.Ample.nonvanishingLocus_congr` moves a nonvanishing locus along an
isomorphism of modules.

`Stacks.CoordinateDictionary.preimage_basicOpen_eq_nvCover` is the same identification for an
arbitrary morphism to the `Proj` of a graded ring generated in degree one, stated with the
isomorphism and the matching of sections as hypotheses. The statements below are at the canonical
morphism of Tag 01ND, where both are produced rather than assumed.

The range statement is phrased with `RingHom.range` of the stalk map rather than as an equation,
because the witness on projective space — the germ of the degree-zero fraction `T_j / Tᵢ` on
`D₊(Tᵢ)` — is only canonical up to the identification of `Γ(D₊(Tᵢ), 𝒪)` with the degree-zero
part of the localisation, and no consumer needs more than membership.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ModuleStalk
open Stacks.SectionsToProjectiveSpace (coordGrading X_mem_coordGrading_one)
open Stacks.AmpleProjectiveImmersion (twistingSheafAtUniverse)
open Stacks.TwistPullbackPinned (coordFrac pullbackCoordSection appLE_apply
  appLE_coordFrac_chart nvCover_le_preimage_basicOpen)

universe u

namespace Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}}

/-! ### Nonvanishing at the generic point of an integral scheme -/

/-- **The submodule `𝔪_x · M_x` at the generic point of an integral scheme is zero**: the local
ring there is the function field. -/
theorem maximalSmul_genericPoint_eq_bot [IsIntegral X] (M : X.Modules) :
    maximalSmul M (genericPoint X) = ⊥ := by
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField X.functionField)
  rw [maximalSmul, hmax, Submodule.bot_smul]

/-- **A global section with nonzero germ at the generic point of an integral scheme does not
vanish there.** Nonvanishing at `x` asks the germ to avoid `𝔪_x · M_x`, which at the generic
point is the zero submodule. -/
theorem mem_nvOpen_genericPoint_of_germ_ne_zero [IsIntegral X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {u : Γ(M, ⊤)}
    (hu : (M.presheaf.Γgerm (genericPoint X)).hom u ≠ 0) :
    genericPoint X ∈ nvOpen M u := by
  rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff X M u,
    maximalSmul_genericPoint_eq_bot M]
  simpa only [Submodule.mem_bot] using hu

/-! ### Ratios under a morphism of modules -/

/-- **A morphism of invertible modules matching two families of global sections matches their
ratios**, at any point of both charts. Over the intersection of the two charts both ratios
multiply the restriction of `vᵢ` to the restriction of `v_k`: for the first one because the
morphism is semilinear, for the second by definition. -/
theorem germ_ratio_eq_of_app_eq {M M' : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
    [Stacks.Ample.IsInvertibleModule X M'] (j : M ⟶ M') {ι : Type*} (u : ι → Γ(M, ⊤))
    (v : ι → Γ(M', ⊤)) (huv : ∀ k, j.app ⊤ (u k) = v k) (i k : ι) {x : X}
    (hx : x ∈ nvCover u i) (hx' : x ∈ nvOpen M' (v i)) :
    X.presheaf.germ (nvCover u i) x hx (ratio u i k) =
      X.presheaf.germ (nvOpen M' (v i)) x hx' (ratio v i k) := by
  set W : X.Opens := nvCover u i ⊓ nvOpen M' (v i)
  have h1 : W ≤ nvCover u i := inf_le_left
  have h2 : W ≤ nvOpen M' (v i) := inf_le_right
  have hxW : x ∈ W := ⟨hx, hx'⟩
  have hjres : ∀ (t : Γ(M, ⊤)), j.app W (resT W t) = resT W (j.app ⊤ t) :=
    fun t => PresheafOfModules.app_resLE j.val le_top t
  have hkey : resO h1 (ratio u i k) = resO h2 (ratio v i k) := by
    refine eq_of_smul_eq_smul (v i) h2 ?_
    rw [resO_ratio_smul v h2 k, ← huv i, ← hjres (u i), ← Scheme.Modules.Hom.app_smul,
      resO_ratio_smul u h1 k, hjres (u k), huv k]
  exact (X.presheaf.germ_res_apply (homOfLE h1) x hxW _).symm.trans
    ((congrArg _ hkey).trans (X.presheaf.germ_res_apply (homOfLE h2) x hxW _))

/-! ### The charts of the morphism of Tag 01ND -/

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}

/-- **The germ of the ratio `s_j / sᵢ` is pulled back from projective space.** The witness is the
germ at `φ x` of the degree-zero fraction `T_j / Tᵢ` on the standard open `D₊(Tᵢ)`: the pullback
of that fraction along `φ` is the ratio, which is
`Stacks.TwistPullbackPinned.appLE_coordFrac_chart` at the pinning of `φ`. -/
theorem germ_ratio_mem_range_stalkMap (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    (i j : Fin (n + 1)) {x : X} (hx : x ∈ nvCover s i) :
    X.presheaf.germ (nvCover s i) x hx (ratio s i j) ∈
      ((toProjectiveSpaceAtUniverse s hs).stalkMap x).hom.range := by
  set g : X ⟶ projectiveSpaceAtUniverse.{u} n := toProjectiveSpaceAtUniverse s hs
  have hpin : (nvCover s i).ι ≫ g = Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
      (chartRatio s i) (span_range_chartRatio s i) := ι_toProjectiveSpaceAtUniverse s hs i
  have hle := nvCover_le_preimage_basicOpen s g i hpin
  refine RingHom.mem_range.mpr ⟨(projectiveSpaceAtUniverse.{u} n).presheaf.germ
    (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) (g.base x)
    (hle hx) ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
      (MvPolynomial.X i)).hom (coordFrac.{u} i j)), ?_⟩
  have hratio := (appLE_coordFrac_chart s g i j hpin).symm.trans
    (appLE_apply g (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
      (nvCover s i) hle ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
        (MvPolynomial.X i)).hom (coordFrac.{u} i j)))
  rw [hratio, X.presheaf.germ_res_apply (homOfLE hle) x hx]
  exact Scheme.Hom.germ_stalkMap_apply g _ x (hle hx) _

/-- **The `i`-th chart of `φ_{(L, (s₀, …, sₙ))}` is the inverse image of the `i`-th standard
open** `D₊(Tᵢ)` of projective space. The inverse image is the nonvanishing open of the pulled
back coordinate `φ^* Tᵢ` in `φ^* 𝒪(1)`, and the twist comparison of [Stacks, Tag 01NE] is an
isomorphism `φ^* 𝒪(1) ≅ L` carrying `φ^* Tᵢ` to `sᵢ`, which moves that nonvanishing open to
`X_{sᵢ}`. -/
theorem preimage_basicOpen_eq_nvCover_canonical (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) (i : Fin (n + 1)) :
    toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) =
      nvCover s i := by
  obtain ⟨α, _, hα⟩ :=
    AlgebraicGeometry.exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse s hs
  rw [← Stacks.ProjectiveSpaceModuli.nvOpen_pullbackCoordSection
    (toProjectiveSpaceAtUniverse s hs) i]
  refine TopologicalSpace.Opens.ext ?_
  show Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback (toProjectiveSpaceAtUniverse s hs)).obj
        (twistingSheafAtUniverse.{u} n))
      (pullbackCoordSection.{u} (toProjectiveSpaceAtUniverse s hs) i) =
    Stacks.Ample.nonvanishingLocus L (s i)
  rw [← hα i]
  exact (Stacks.Ample.nonvanishingLocus_congr (asIso α)
    (pullbackCoordSection.{u} (toProjectiveSpaceAtUniverse s hs) i)).symm

/-- **The inverse image of `D₊(Tᵢ)` lies in the chart `X_{sᵢ}`**, the converse of
`Stacks.TwistPullbackPinned.nvCover_le_preimage_basicOpen` at the canonical morphism. -/
theorem preimage_basicOpen_le_nvCover_canonical (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) (i : Fin (n + 1)) :
    toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) ≤
      nvCover s i :=
  (preimage_basicOpen_eq_nvCover_canonical s hs i).le

end Stacks.ProjectiveFromSections

end
