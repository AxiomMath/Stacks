module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection

/-!
# The canonical section vanishes along a morphism into the divisor

Let `D` be an effective Cartier divisor on a scheme `X` and `f : Y ⟶ X` a morphism through which
the ideal of `D` pulls back to zero, that is, `D ≤ ker f`. Then the pullback along `f` of the
canonical section `1_D` of `𝒪_X(D)` is zero.

## Main results

* `Stacks.Divisors.exists_affineOpen_canonicalSection_eq_smul`: locally on affine opens the
  canonical section is `a • w` with `a` in the ideal of `D`.
* `Stacks.Divisors.pullbackSectionHom_canonicalSection_eq_zero`: if `D ≤ ker f`, the pullback along
  `f` of the canonical section is zero.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X Y : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (f : Y ⟶ X)

omit [IsEffectiveCartierDivisor D] in
/-- Restricting a pulled-back section to a smaller open of the source is pulling it back to that
open directly. -/
theorem pullbackSectionHom_res (M : X.Modules) (U : X.Opens) {V V' : Y.Opens} (hV'V : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV'V).op
        (pullbackSectionHom f M U V h a) = pullbackSectionHom f M U V' h' a := by
  change ConcreteCategory.hom (((Scheme.Modules.pullback f).obj M).val.map (homOfLE hV'V).op)
      (ConcreteCategory.hom (((Scheme.Modules.pullback f).obj M).val.map (homOfLE h).op)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U a)) =
    ConcreteCategory.hom (((Scheme.Modules.pullback f).obj M).val.map (homOfLE h').op)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U a)
  exact (PresheafOfModules.map_comp_apply (((Scheme.Modules.pullback f).obj M).val)
    (homOfLE h).op (homOfLE hV'V).op _).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)

/-- **Locally the canonical section is a multiple by an element of the ideal.** Every point has
an affine neighbourhood `V` on which `1_D|_V = a • w` with `a ∈ ℐ_D(V)`. -/
theorem exists_affineOpen_canonicalSection_eq_smul (x : X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), x ∈ V ∧ ∃ (a : Γ(X, V)) (w : Γ(divisorSheaf D, V)),
      a ∈ D.ideal ⟨V, hV⟩ ∧ (canonicalSection' D).val (op V) = a • w := by
  obtain ⟨U, hU, hxU, g, hg, hgen⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D ‹_› x
  obtain ⟨y, hy⟩ := (mem_ideal_iff_exists_idealSheafSection D ⟨U, hU⟩ g).1
    (hgen ▸ Ideal.mem_span_singleton_self g)
  let b := Stacks.SheafOfModules.DualBasisOne.ofSmulBijective U y
    (bijective_smulSectionMap_resSection D ⟨U, hU⟩ hgen hg.mem_nonZeroDivisors hy)
  refine ⟨U, hU, hxU, g, b.lam, hgen ▸ Ideal.mem_span_singleton_self g, ?_⟩
  exact (eq_smul_dualBasisOne_lam D b ((canonicalSection' D).val (op U))).symm.trans
    (congrArg (fun c : Γ(X, U) ↦ c • (show Γ(divisorSheaf D, U) from b.lam))
      ((dualEvalLinearMap_canonicalSection D b).trans hy))

/-- **The canonical section vanishes along a morphism into the divisor**: if `D ≤ ker f`, the
pullback along `f` of the canonical section `1_D` is zero. -/
theorem pullbackSectionHom_canonicalSection_eq_zero (hf : D ≤ f.ker) :
    pullbackSectionHom f (invertibleSheaf' D) ⊤ ⊤ (by simp)
      ((canonicalSection' D).val (op ⊤)) = 0 := by
  set N := (Scheme.Modules.pullback f).obj (invertibleSheaf' D)
  refine TopCat.Presheaf.section_ext ⟨N.presheaf, N.isSheaf⟩ ⊤ _ 0 fun y _ ↦ ?_
  obtain ⟨V, hV, hxV, a, w, ha, heq⟩ := exists_affineOpen_canonicalSection_eq_smul D (f y)
  have hyV : y ∈ f ⁻¹ᵁ V := hxV
  have hres := pullbackSectionHom_res f (invertibleSheaf' D) ⊤ (le_top : f ⁻¹ᵁ V ≤ ⊤)
    (by simp) (by simp) ((canonicalSection' D).val (op ⊤))
  have hmap := pullbackSectionHom_map f (invertibleSheaf' D) ⊤ V le_top (f ⁻¹ᵁ V) le_rfl
    (by simp) ((canonicalSection' D).val (op ⊤))
  have hsec : (invertibleSheaf' D).val.map (homOfLE (le_top : V ≤ ⊤)).op
      ((canonicalSection' D).val (op ⊤)) = (canonicalSection' D).val (op V) :=
    PresheafOfModules.sections_property (canonicalSection' D) _
  have hzero : f.appLE V (f ⁻¹ᵁ V) le_rfl a = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply,
      show (f.app V).hom a = 0 from f.ideal_ker_le ⟨V, hV⟩ (hf ⟨V, hV⟩ ha), map_zero]
  have hloc : N.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op
      (pullbackSectionHom f (invertibleSheaf' D) ⊤ ⊤ (by simp)
        ((canonicalSection' D).val (op ⊤))) = 0 := by
    refine hres.trans (hmap.symm.trans ((congrArg (pullbackSectionHom f (invertibleSheaf' D) V
      (f ⁻¹ᵁ V) le_rfl) (hsec.trans heq)).trans
        ((pullbackSectionHom_smul f (divisorSheaf D) V (f ⁻¹ᵁ V) le_rfl a w).trans ?_)))
    rw [hzero, zero_smul]
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)) y hyV, hloc,
    map_zero, map_zero]

end Stacks.Divisors

end
