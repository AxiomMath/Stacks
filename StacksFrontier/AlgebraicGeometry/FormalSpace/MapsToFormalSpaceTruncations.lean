module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AdicCompleteMonoSection
public import StacksFrontier.Deformation.Artin.FunctorFormalObject

/-!
# Sections of a formal algebraic space over a complete local ring are determined by truncations

Let `W` be a formal algebraic space over `S` and `R` a Noetherian complete local `S`-algebra with
residue field of finite type over `S`. Two sections of `W` over `Spec R` which agree on every
infinitesimal thickening `Spec(R/𝔪ⁿ⁺¹)` are equal. This is the injectivity half of Stacks 0AQH
with a formal algebraic space as target, and it holds for the same reason: by Stacks 0AIP the
diagonal of `W` is representable, so the locus where the two sections agree is a scheme `T`
mapping by a monomorphism to `Spec R`; it has a section over every thickening, hence, `R` being
complete, over `Spec R`.

## Main results

* `AlgebraicGeometry.FormalSpace.eq_of_forall_restrictionToBase_eq`: the statement above.

## References

* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing Deformation.Artin

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A section of the underlying scheme morphism of a morphism of the site is a section in the
site. -/
theorem exists_siteHom_section_of_toScheme {T V : BigFppfOver B S hS} (q : T ⟶ V)
    (σ : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hσ : σ ≫ (BigFppfOver.toScheme B S hS).map q = 𝟙 _) :
    ∃ τ : V ⟶ T, τ ≫ q = 𝟙 V := by
  obtain ⟨σ₀, hmap⟩ : ∃ r : V.left ⟶ T.left, B.inclusion.map r = σ :=
    ⟨B.inclusion.preimage σ, B.inclusion.map_preimage σ⟩
  have h₁ : σ₀ ≫ q.left = 𝟙 V.left := by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, hmap, B.inclusion.map_id]
  exact ⟨Over.homMk σ₀ (by rw [← Over.w q, ← Category.assoc, h₁, Category.id_comp]),
    Over.OverMorphism.ext h₁⟩

/-- **Sections of a formal algebraic space over a complete local base are determined by their
truncations.** Two sections of a formal algebraic space `W` over `Spec R`, for `R` a Noetherian
complete local `S`-algebra with residue field of finite type over `S`, which agree on every
thickening `Spec(R/𝔪ⁿ⁺¹)`, are equal. -/
theorem eq_of_forall_restrictionToBase_eq {W : FppfSheaf B S hS}
    (hW : IsFormalAlgebraicSpace B S hS W) (A : FormalBase S)
    (hA : ∀ n, B.Contains (A.truncation n))
    {x y : W.obj.obj (op (baseOver B S hS A (A.contains_spec_of_contains_truncation hA)))}
    (h : ∀ n, W.obj.map (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA)
      hA n).op x = W.obj.map (restrictionToBase B S hS A
        (A.contains_spec_of_contains_truncation hA) hA n).op y) :
    x = y := by
  classical
  have : IsAdicComplete (maximalIdeal A.R) A.R := A.complete
  have hRS := A.contains_spec_of_contains_truncation hA
  let V := baseOver B S hS A hRS
  let J := BigFppfOver.topology B S hS
  let hrep := relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hW
  let α : (Sheaf.sheafifiedYoneda J).obj V ⟶ W := (Sheaf.sectionEquiv J).symm x
  let β : (Sheaf.sheafifiedYoneda J).obj V ⟶ W := (Sheaf.sectionEquiv J).symm y
  let g : (Sheaf.sheafifiedYoneda J).obj V ⟶ W ⨯ W := prod.lift α β
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) := by
    have hdiag : (MorphismProperty.monomorphisms _) (diag W) :=
      inferInstanceAs (Mono (diag W))
    have : Mono ((Sheaf.sheafifiedYoneda J).map (hrep.snd g)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hrep.isPullback g) hdiag
    have : Mono (hrep.snd g) := (Sheaf.sheafifiedYoneda J).mono_of_mono_map this
    exact preserves_mono_of_preservesLimit _ (hrep.snd g)
  -- a section of the projection over every truncation
  have hsec : ∀ n : ℕ, ∃ s : Spec (.of (A.R ⧸ maximalIdeal A.R ^ n)) ⟶
      (BigFppfOver.toScheme B S hS).obj (hrep.pullback g),
      s ≫ (BigFppfOver.toScheme B S hS).map (hrep.snd g) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ n))) := by
    intro n
    let ι := restrictionToBase B S hS A hRS hA n
    have hab : (Sheaf.sheafifiedYoneda J).map ι ≫ α = (Sheaf.sheafifiedYoneda J).map ι ≫ β := by
      apply (Sheaf.sectionEquiv J).injective
      rw [Sheaf.sectionEquiv_map_comp, Sheaf.sectionEquiv_map_comp]
      simpa only [α, β, Equiv.apply_symm_apply] using h n
    have hi : ((Sheaf.sheafifiedYoneda J).map ι ≫ α) ≫ diag W =
        (Sheaf.sheafifiedYoneda J).map ι ≫ g := by
      refine prod.hom_ext ?_ ?_
      · simp only [g, Category.assoc, diag, prod.lift_fst, Category.comp_id]
      · simpa only [g, Category.assoc, diag, prod.lift_snd, Category.comp_id] using hab
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ n)))) ≫
      (BigFppfOver.toScheme B S hS).map (hrep.lift _ ι hi), ?_⟩
    have e1 : (BigFppfOver.toScheme B S hS).map (hrep.lift _ ι hi) ≫
        (BigFppfOver.toScheme B S hS).map (hrep.snd g) = (BigFppfOver.toScheme B S hS).map ι := by
      rw [← Functor.map_comp, hrep.lift_snd]
    have e2 : (BigFppfOver.toScheme B S hS).map ι =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))) := rfl
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (e1.trans e2)).trans ?_)
    exact (Spec.map_comp _ _).symm
  choose s hs using hsec
  obtain ⟨σ, hσ⟩ := @exists_section_of_mono_of_forall_section_quotient_pow A.R _
    (maximalIdeal A.R) (maximalIdeal.isMaximal A.R) _ _
    ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) hmono s hs
  obtain ⟨τ, hτ⟩ := exists_siteHom_section_of_toScheme (hrep.snd g) σ hσ
  have hfac : ((Sheaf.sheafifiedYoneda J).map τ ≫ hrep.fst g) ≫ diag W = g := by
    rw [Category.assoc, (hrep.isPullback g).w, ← Category.assoc, ← Functor.map_comp, hτ,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hαβ : α = β := by
    have h₁ := congrArg (fun t => t ≫ Limits.prod.fst) hfac
    have h₂ := congrArg (fun t => t ≫ Limits.prod.snd) hfac
    simp only [g, Category.assoc, prod.lift_fst, prod.lift_snd, diag, Category.comp_id] at h₁ h₂
    exact h₁.symm.trans h₂
  exact (Sheaf.sectionEquiv J).symm.injective hαβ

end AlgebraicGeometry.FormalSpace

end
