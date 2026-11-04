module

public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Completion
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Functor

/-!
# The effective formal object of Stacks Example 98.12.8

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal, `R = Λ_𝔪^∧`, and `Λ → C → R` a
factorization with `C` of finite type over `Λ`. The spectrum `Spec R → S = Spec Λ` factors
through `Spec C → S' = (S ∖ {𝔪}) ⨿ Spec C`, so it carries an object of the category `𝒳 = 𝒮_F`
of the Example. Restricting that object to the infinitesimal thickenings of the closed point
gives a formal object `ξ` of `𝒳` over `R`, which is effective by construction.

## Main definitions

* `Deformation.Artin.GRingNecessity.completionBase`: `R = Λ_𝔪^∧` as a complete local base
  over `S`.
* `Deformation.Artin.GRingNecessity.completionLocalObject`: the object of `𝒳` over `Spec R`.
* `Deformation.Artin.GRingNecessity.formalObject`: the formal object `ξ` of `𝒳` over `R`.
* `Deformation.Artin.GRingNecessity.IsCompletionBase`: a complete local base over `S` is
  isomorphic over `S` to `Spec R`.

## Main results

* `Deformation.Artin.GRingNecessity.formalObject_isEffective`: `ξ` is effective.
* `Deformation.Artin.GRingNecessity.isCompletionBase_formalObject`: the base of `ξ` is
  isomorphic over `S` to `Spec R`.

## Implementation notes

The formal object is the image of the object over `Spec R` under the library's approximation
functor, whose value has as base the complete local ring chosen for that object; that choice
is isomorphic to `R` over `S`, and `IsCompletionBase` records exactly this, which is all the
later arguments use about the base.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory IsLocalRing Cardinal

universe u

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]

/-! ### The complete local base `Spec Λ_𝔪^∧ → Spec Λ` -/

section Base

variable [IsNoetherianRing Λ]

/-- `Λ → Λ_𝔪^∧ / 𝔪_R ^ n` is surjective, as a statement about the quotient map. -/
theorem completion_quotient_surjective (n : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal (Completion 𝔪) ^ n)).comp
      (algebraMap Λ (Completion 𝔪))) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨l, hl⟩ := exists_sub_mem_pow_completion 𝔪 n r
  exact ⟨l, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by rwa [← neg_mem_iff, neg_sub])⟩

/-- The complete local ring `R = Λ_𝔪^∧` with its structure morphism `Spec R → Spec Λ`. -/
def completionBase : FormalBase (Spec (.of Λ)) where
  R := Completion 𝔪
  noetherian := inferInstance
  complete := inferInstance
  toS := Spec.map (CommRingCat.ofHom (algebraMap Λ (Completion 𝔪)))
  residueLocallyFiniteType := by
    rw [adicThickeningι, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (completion_quotient_surjective 𝔪 (0 + 1))
  residueQuasiCompact := inferInstance

/-- The ring of `completionBase 𝔪` is `Λ_𝔪^∧`. -/
@[simp]
theorem completionBase_R : (completionBase 𝔪).R = Completion 𝔪 := rfl

/-- The structure morphism of `completionBase 𝔪` is the spectrum of `Λ → Λ_𝔪^∧`. -/
@[simp]
theorem completionBase_toS :
    (completionBase 𝔪).toS = Spec.map (CommRingCat.ofHom (algebraMap Λ (Completion 𝔪))) :=
  rfl

omit [IsNoetherianRing Λ] in
/-- `Λ_𝔪` has at most the size of `Spec Λ`. -/
theorem mk_localization_le_size :
    #(Localization.AtPrime 𝔪) ≤ (Spec (.of Λ)).size := by
  rw [Scheme.size_Spec]
  exact Cardinal.mk_le_of_isLocalization 𝔪.primeCompl _

omit [IsNoetherianRing Λ] in
/-- The spectrum of `Λ_𝔪^∧` lies in every big fppf site containing `Spec Λ`. -/
theorem completion_contains (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ))) :
    B.Contains (Spec (.of (Completion 𝔪))) := by
  apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hS
  set I := maximalIdeal (Localization.AtPrime 𝔪)
  set Q : ℕ → Type u := fun n =>
    Localization.AtPrime 𝔪 ⧸ (I ^ n • (⊤ : Submodule (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪)))
  calc #(CommRingCat.of (Completion 𝔪)) ≤ #(∀ n : ℕ, Q n) :=
        mk_le_of_injective (f := fun x : AdicCompletion I (Localization.AtPrime 𝔪) => x.val)
          Subtype.val_injective
    _ = Cardinal.prod (fun n : ℕ => #(Q n)) := mk_pi _
    _ ≤ Cardinal.prod (fun _ : ℕ => (Spec (.of Λ)).size) :=
        prod_le_prod _ _ fun _ => mk_quotient_le.trans (mk_localization_le_size 𝔪)
    _ = (Spec (.of Λ)).size ^ ℵ₀ := by simp

end Base

/-! ### The object over `Spec Λ_𝔪^∧` and the formal object -/

section Object

variable (C : Type u) [CommRing C] [Algebra Λ C]

/-- A `Λ`-algebra map `C → X` makes `Spec X → Spec Λ` factor through `S'`, via
`Spec X → Spec C → S'`. -/
theorem factorsThrough_of_algHom {X : Type u} [CommRing X] [Algebra Λ X] (ψ : C →ₐ[Λ] X) :
    FactorsThroughPuncturedCoprod 𝔪 C (Spec.map (CommRingCat.ofHom (algebraMap Λ X))) := by
  refine ⟨Spec.map (CommRingCat.ofHom (ψ : C →+* X)) ≫ Limits.coprod.inr, ?_⟩
  rw [Category.assoc, inr_puncturedCoprodMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.comp_algebraMap]

variable [IsNoetherianRing Λ] (φ : C →ₐ[Λ] Completion 𝔪) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of Λ)))

/-- `Spec Λ_𝔪^∧` as an object of the big fppf site of `S = Spec Λ`. -/
abbrev completionOver : BigFppfOver B (Spec (.of Λ)) hS :=
  baseOver B (Spec (.of Λ)) hS (completionBase 𝔪) (completion_contains 𝔪 B hS)

/-- The object of `𝒳` over `Spec Λ_𝔪^∧` given by `Spec Λ_𝔪^∧ → Spec C → S'`. -/
def completionObj : (factorizationCategory 𝔪 C B hS).val.obj :=
  mkObj 𝔪 C B hS (completionOver 𝔪 B hS) (factorsThrough_of_algHom 𝔪 C φ)

/-- The object of `𝒳` over `Spec Λ_𝔪^∧`, as an object over a complete local base. -/
def completionLocalObject :
    CompleteLocalObjects B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p :=
  ⟨⟨completionObj 𝔪 C φ B hS, ⟨completionBase 𝔪, completion_contains 𝔪 B hS, rfl⟩⟩⟩

/-- **The formal object `ξ` of Stacks Example 98.12.8**: the restrictions of the object of `𝒳`
over `Spec Λ_𝔪^∧` to the infinitesimal thickenings of the closed point. -/
def formalObject : FormalObject B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p :=
  (approximationFunctor B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
    (factorizationCategory 𝔪 C B hS).property).obj (completionLocalObject 𝔪 C φ B hS)

/-- **Stacks Example 98.12.8: the formal object `ξ` is effective.** It is the image of the
object of `𝒳` over `Spec Λ_𝔪^∧` under the approximation functor. -/
theorem formalObject_isEffective :
    FormalObject.IsEffective B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
      (factorizationCategory 𝔪 C B hS).property (formalObject 𝔪 C φ B hS) :=
  ⟨completionLocalObject 𝔪 C φ B hS, ⟨Iso.refl _⟩⟩

end Object

/-! ### Complete local bases isomorphic to `Spec Λ_𝔪^∧` -/

section CompletionBase

variable [IsNoetherianRing Λ]

/-- A complete local base over `S = Spec Λ` is isomorphic over `S` to `Spec Λ_𝔪^∧`: there is a
ring isomorphism `σ : Λ_𝔪^∧ ≅ A` such that the structure morphism of `A` is the spectrum of
`σ ∘ (Λ → Λ_𝔪^∧)`. -/
def IsCompletionBase (A : FormalBase (Spec (.of Λ))) : Prop :=
  ∃ σ : Completion 𝔪 ≃+* A.R,
    Spec.map (CommRingCat.ofHom ((σ : Completion 𝔪 →+* A.R).comp
      (algebraMap Λ (Completion 𝔪)))) = A.toS

/-- `completionBase 𝔪` is isomorphic to `Spec Λ_𝔪^∧` over `S`, by the identity. -/
theorem isCompletionBase_completionBase : IsCompletionBase 𝔪 (completionBase 𝔪) :=
  ⟨RingEquiv.refl _, rfl⟩

omit [IsNoetherianRing Λ] [𝔪.IsMaximal] in
/-- Two complete local bases with the same spectrum over `S` in the site are isomorphic over
`S`. -/
theorem exists_ringEquiv_of_baseOver_eq (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
    {A A' : FormalBase (Spec (.of Λ))} {hA : B.Contains (Spec (.of A.R))}
    {hA' : B.Contains (Spec (.of A'.R))}
    (h : baseOver B (Spec (.of Λ)) hS A' hA' = baseOver B (Spec (.of Λ)) hS A hA) :
    ∃ σ : A.R ≃+* A'.R,
      Spec.map (CommRingCat.ofHom (σ : A.R →+* A'.R)) ≫ A.toS = A'.toS := by
  have hl : B.obj hA' = B.obj hA := congrArg Over.left h
  have hs : Spec (.of A'.R) = Spec (.of A.R) :=
    congrArg ObjectProperty.FullSubcategory.obj hl
  have hw : eqToHom hs ≫ A.toS = A'.toS := by
    have h1 := congrArg (fun f => B.inclusion.map f) (Over.w (eqToHom h))
    simp only [Functor.map_comp, Over.eqToHom_left, eqToHom_map] at h1
    exact h1
  let φ₁ : CommRingCat.of A.R ⟶ CommRingCat.of A'.R := Spec.preimage (eqToHom hs)
  let φ₂ : CommRingCat.of A'.R ⟶ CommRingCat.of A.R := Spec.preimage (eqToHom hs.symm)
  have h12 : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by simp [φ₁, φ₂])
  have h21 : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by simp [φ₁, φ₂])
  refine ⟨RingEquiv.ofRingHom φ₁.hom φ₂.hom (congrArg CommRingCat.Hom.hom h21)
    (congrArg CommRingCat.Hom.hom h12), ?_⟩
  change Spec.map (CommRingCat.ofHom φ₁.hom) ≫ A.toS = A'.toS
  rwa [CommRingCat.ofHom_hom, Spec.map_preimage]

variable (C : Type u) [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] Completion 𝔪)
  (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- The object of `𝒳` underlying `completionLocalObject` lies over `Spec Λ_𝔪^∧`. -/
theorem p_obj_completionLocalObject :
    (factorizationCategory 𝔪 C B hS).val.p.obj (completionLocalObject 𝔪 C φ B hS).obj.1 =
      completionOver 𝔪 B hS :=
  rfl

/-- The base of `ξ` is the complete local base chosen for the object over `Spec Λ_𝔪^∧`. -/
theorem formalObject_base :
    (formalObject 𝔪 C φ B hS).base =
      chosenBase B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
        (completionLocalObject 𝔪 C φ B hS).obj := by
  obtain ⟨-, hbase, -⟩ := (approximationFunctorData B (Spec (.of Λ)) hS
    (factorizationCategory 𝔪 C B hS).val.p (factorizationCategory 𝔪 C B hS).property).2
  exact hbase _

/-- The base of the formal object `ξ` is isomorphic over `S` to `Spec Λ_𝔪^∧`. -/
theorem isCompletionBase_formalObject :
    IsCompletionBase 𝔪 (formalObject 𝔪 C φ B hS).base := by
  rw [formalObject_base]
  have heq : baseOver B (Spec (.of Λ)) hS
      (chosenBase B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
        (completionLocalObject 𝔪 C φ B hS).obj)
      (chosenContains B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
        (completionLocalObject 𝔪 C φ B hS).obj) = completionOver 𝔪 B hS :=
    (chosenBase_eq B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
      (completionLocalObject 𝔪 C φ B hS).obj).symm.trans
      (p_obj_completionLocalObject 𝔪 C φ B hS)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_baseOver_eq B hS heq
  exact ⟨σ, ((congrArg Spec.map (CommRingCat.ofHom_comp _ _)).trans (Spec.map_comp _ _)).trans hσ⟩

end CompletionBase

end Deformation.Artin.GRingNecessity

end
