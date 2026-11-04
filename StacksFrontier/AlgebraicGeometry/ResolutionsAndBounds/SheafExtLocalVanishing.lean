module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SheafExtStalkVanishing

/-!
# Local vanishing of sheaf Ext's on a locally Noetherian scheme

Let `X` be a locally Noetherian scheme, `G` an `𝒪_X`-module with an injective resolution `I^•`,
`A` an `𝒪_X`-module coherent near a point `y`, and suppose that the stalk `A_y` has projective
dimension at most `e` over the local ring at `y`. Then the sheaf Ext's `𝓔xt^q(A, G)` vanish on a
neighbourhood of `y` for every `q > e`.

The proof is by induction on `e`, along the syzygy sequences of
`Stacks.SheafHomInjective.exists_syzygy`. When `e = 0` the stalk `A_y` is projective, hence free
over the local ring, and `A` is free near `y` by [Stacks, Tag 0B8J]; the sheaf Ext's of a free
module vanish in positive degrees. For the inductive step, a syzygy `K` of `A` near `y` has
projective dimension at most `e - 1` at `y`, and the long exact sequence of sheaf Ext's shifts
the vanishing of `𝓔xt^q(K, G)` to that of `𝓔xt^{q+1}(A, G)`.

## Main results

* `Stacks.SheafHomInjective.exists_vanishesOn_homology_of_hasProjectiveDimensionLT`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafHomInjective

variable {X : Scheme.{u}}

/-- A monomorphism whose cokernel vanishes near `y` induces an isomorphism on stalks at `y`. -/
private theorem isIso_stalk_map_of_mono_of_vanishesOn_cokernel
    {E E' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)} (f : E ⟶ E')
    [Mono f] {U : X.Opens} (hc : VanishesOn (cokernel f) U) {y : X} (hy : y ∈ U) :
    IsIso ((stk y).map f) :=
  isIso_stalk_map_of_vanishesOn f (vanishesOn_of_isZero (isZero_kernel_of_mono f) U) hc hy

/-- **Local vanishing of sheaf Ext's.** Let `X` be locally Noetherian and let `A` be coherent on
`W ∋ y` with `pd A_y < e + 1`. Then `𝓔xt^{q+e+1}(A, G)` vanishes on a neighbourhood of `y` for
every `q`. -/
theorem exists_vanishesOn_homology_of_hasProjectiveDimensionLT [IsLocallyNoetherian X]
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
    (Res : InjectiveResolution G) (y : X) (e : ℕ) :
    ∀ (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (W : X.Opens),
      Stacks.SheafOfModules.IsCoherentOn A W → y ∈ W →
      HasProjectiveDimensionLT ((stk y).obj A) (e + 1) →
      ∃ U : X.Opens, y ∈ U ∧
        ∀ q : ℕ, VanishesOn ((cx X.sheaf A Res.cocomplex).homology (q + e + 1)) U := by
  have hO : Stacks.SheafOfModules.IsCoherent
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := X))
  induction e with
  | zero =>
    intro A W hA hy hpd
    obtain ⟨U₀, hy₀, -, ι, hι, P, i, π, hi, hci, hcπ, -⟩ := exists_syzygy hA hy
    have hSi := isIso_stalk_map_of_mono_of_vanishesOn_cokernel i hci hy₀
    have hSπ : Epi ((stk y).map π) := (shortExact_stalk_kernel π hcπ hy₀).epi_g
    have hprojA : Projective ((stk y).obj A) :=
      projective_iff_hasProjectiveDimensionLT_one.2 hpd
    let p : (stk y).obj (SheafOfModules.free ι) ⟶ (stk y).obj A :=
      inv ((stk y).map i) ≫ (stk y).map π
    have hp : Epi p := epi_comp _ _
    obtain ⟨ρ, hρ, ⟨bas⟩⟩ := exists_basis_of_projective (basisStalkFree ι y) p hp hprojA
    obtain ⟨LP⟩ := nonempty_localPresentation_of_isCoherentOn (X := X.toTopCat) (O := X.sheaf)
      hA hy
    obtain ⟨U, hyU, ⟨eU⟩⟩ :=
      Stacks.SheafOfModules.nonempty_over_iso_free_of_localPresentation A y LP bas
    exact ⟨U, hyU, fun q => vanishesOn_homology_of_over_iso_free Res eU q⟩
  | succ e ih =>
    intro A W hA hy hpd
    obtain ⟨U₀, hy₀, -, ι, hι, P, i, π, hi, hci, hcπ, hK⟩ := exists_syzygy hA hy
    have hSi := isIso_stalk_map_of_mono_of_vanishesOn_cokernel i hci hy₀
    have hP : Projective ((stk y).obj P) :=
      Projective.of_iso (asIso ((stk y).map i)).symm (projective_stalk_free ι y)
    have hS := shortExact_stalk_kernel π hcπ hy₀
    have hP' : HasProjectiveDimensionLT ((stk y).obj P) (e + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (e + 1) (by omega)
    have hKpd : HasProjectiveDimensionLT ((stk y).obj (kernel π)) (e + 1) :=
      hS.hasProjectiveDimensionLT_X₁ (e + 1) hP' hpd
    obtain ⟨U₁, hy₁, hU₁⟩ := ih (kernel π) U₀ hK hy₀ hKpd
    refine ⟨U₀ ⊓ U₁, ⟨hy₀, hy₁⟩, fun q => ?_⟩
    rw [show q + (e + 1) + 1 = q + e + 1 + 1 by omega]
    exact vanishesOn_homology_succ_of_cokernel Res π (q + e + 1) (hcπ.mono inf_le_left)
      ((vanishesOn_homology_of_mono_free Res i hci (q + e + 1)).mono inf_le_left)
      ((hU₁ q).mono inf_le_right)

end Stacks.SheafHomInjective

end
