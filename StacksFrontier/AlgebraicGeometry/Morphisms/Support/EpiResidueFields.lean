module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.EpiOverLocalBase

/-!
# Epimorphisms onto a module of finite type are detected on residue fields

Let `X` be a scheme and `φ : ℳ ⟶ 𝒩` a morphism of `𝒪_X`-modules with `𝒩` of finite type. If the
restriction of `φ` along `Spec κ(x) ⟶ X` is an epimorphism for every point `x`, then `φ` is an
epimorphism. This is Nakayama's lemma in the form used in the proof of Stacks 0DPA, where a map
`𝒪^{⊕ N} ⟶ π_*(𝒬(m))` onto a finite locally free module is shown to be surjective on fibres.

The cokernel of `φ` is of finite type, and its restriction to each `Spec κ(x)` vanishes because
pullback is a left adjoint; the support of the restriction is the inverse image of the support
(Stacks 056J), so no point lies in the support of the cokernel, which therefore vanishes.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isZero_of_forall_isZero_pullback_fromSpecResidueField`.
* `AlgebraicGeometry.Scheme.Modules.epi_of_forall_epi_pullback_fromSpecResidueField`.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **A module of finite type whose restriction to every residue field vanishes, vanishes.** -/
public theorem isZero_of_forall_isZero_pullback_fromSpecResidueField (M : X.Modules)
    (hM : M.IsFiniteType)
    (h : ∀ x : X, IsZero ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M)) :
    IsZero M := by
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty M
    (Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
  let s : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  have hz : s ∈ (X.fromSpecResidueField x).base ⁻¹' SheafOfModules.supp M := by
    show (X.fromSpecResidueField x).base s ∈ SheafOfModules.supp M
    rwa [Scheme.fromSpecResidueField_apply]
  rwa [← SheafOfModules.supp_pullback (X.fromSpecResidueField x) M,
    _root_.SheafOfModules.supp_eq_empty_of_isZero (h x)] at hz

/-- **An epimorphism onto a module of finite type is detected on residue fields.** -/
public theorem epi_of_forall_epi_pullback_fromSpecResidueField {M N : X.Modules} (φ : M ⟶ N)
    (hN : N.IsFiniteType)
    (h : ∀ x : X, Epi ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map φ)) :
    Epi φ := by
  have hc := isZero_of_forall_isZero_pullback_fromSpecResidueField (cokernel φ)
    (isFiniteType_cokernel φ hN) fun x => by
      let : PreservesColimitsOfSize.{u, u}
          (Scheme.Modules.pullback (X.fromSpecResidueField x)) :=
        (Scheme.Modules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits
      have := h x
      exact (isZero_cokernel_of_epi ((Scheme.Modules.pullback _).map φ)).of_iso
        (PreservesCokernel.iso (Scheme.Modules.pullback _) φ)
  exact Abelian.epi_of_cokernel_π_eq_zero φ (hc.eq_of_tgt _ _)

end AlgebraicGeometry.Scheme.Modules

end
