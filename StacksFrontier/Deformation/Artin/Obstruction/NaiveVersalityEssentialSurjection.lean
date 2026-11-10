module

public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Deformation.BaseCategory.EssentialSurjectionDifferential
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential surjections of `𝒞_Λ`, read off the base-change map of differentials

Stacks 06H0 detects an essential surjection `f : B ⟶ A` of the base category `𝒞_Λ` on the
cotangent spaces of the presentations of the residue field: `f` is an essential surjection
exactly when `Ω_{B/Λ} ⊗_B k ⟶ Ω_{A/Λ} ⊗_A k` is an isomorphism. That map is recorded in
`StacksFrontier.Deformation.BaseCategory.EssentialSurjectionDifferential` as
`Algebra.Extension.CotangentSpace.map (residueExtHom f)`, the map of cotangent spaces of the
presentations `Deformation.ArtinianLocalAlgCat.residueExt`.

The same map has a second name in this repository. Stacks 07YL and Stacks 07YM speak of it as
`Deformation.Artin.differentialsBaseChangeMap`, the canonical map
`k ⊗_{A'} Ω_{A'/Λ} ⟶ k ⊗_A Ω_{A/Λ}` attached to a tower `Λ → A' → A → k` of arbitrary
commutative rings; it is in that form that Stacks 07YL asserts the square-zero extension it
builds "does not change differentials modulo `𝔭`". This file identifies the two and so makes
the criterion of Stacks 06H0 available to the consumers of Stacks 07YL.

## Main results

* `Deformation.Artin.tensorKaehlerDifferential_ext` — two `k`-linear maps out of
  `k ⊗_B Ω_{B/Λ}` agree as soon as they agree on the elements `c ⊗ d b`.
* `Deformation.Artin.differentialsBaseChangeMap_tmul_D` — the value of
  `Deformation.Artin.differentialsBaseChangeMap` on `c ⊗ d b`.
* `Deformation.Artin.differentialsBaseChangeMap_comp` — functoriality in the tower: the
  base-change maps of `Λ → A₂ → A₁ → k` and `Λ → A₁ → A₀ → k` compose to the one of
  `Λ → A₂ → A₀ → k`.
* `Deformation.Artin.differentialsBaseChangeMap_eq_cotangentSpaceMap` — the identification:
  for a tower `Λ → B → A → k` in which both `B ⟶ k` and `A ⟶ k` are surjective, the
  base-change map of differentials *is* the map on cotangent spaces of the two presentations
  of `k` over `Λ`.
* `Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`
  — **Stacks 06H0, part (2), conditions (a) and (c)**, with the cotangent space written as the
  base-change map of differentials: a morphism `f : B ⟶ A` of `𝒞_Λ` is an essential surjection
  exactly when `Deformation.Artin.differentialsBaseChangeMap Λ B A k` is bijective.

## Implementation notes

`Deformation.Artin.differentialsBaseChangeMap` is defined as the `k`-linear base change of
`KaehlerDifferential.mapBaseChange` composed with the cancellation
`k ⊗_A (A ⊗_{A'} Ω_{A'/Λ}) ≅ k ⊗_{A'} Ω_{A'/Λ}`, so its value on a generator takes a short
computation; that is `Deformation.Artin.differentialsBaseChangeMap_tmul_D`, and everything
else here is extensionality against it.

The extensionality lemma is stated for maps out of `k ⊗_B Ω_{B/Λ}` for a *plain* ring `B`
rather than for maps out of `P.CotangentSpace` for a presentation `P`. The two types are
definitionally equal when `P = residueExt B`, but `P.Ring` does not reduce to `B` at
`instances` transparency, so an induction performed on the presentation's cotangent space
leaves goals whose module instances cannot be synthesized. For the same reason
`Deformation.Artin.differentialsBaseChangeMap_eq_cotangentSpaceMap` is oriented with the
base-change map on the left: that way the statement elaborates against the plain ring and the
presentation appears only on the right, where `Algebra.Extension.CotangentSpace.map_tmul`
applies directly.

The algebra structure `Algebra B A` and the two scalar towers that a morphism of `𝒞_Λ` carries
depend on the morphism and so cannot be instances;
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`
therefore introduces them with `letI` in its own statement, exactly as
`Deformation.ArtinianLocalAlgCat.residueExtHom` does.

## References

* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Artin

/-! ### Extensionality for maps out of the cotangent space -/

/-- Two `k`-linear maps out of `k ⊗_B Ω_{B/Λ}` agree as soon as they agree on the elements
`c ⊗ d b`.

Those elements do not span the tensor product as a set, but `Ω_{B/Λ}` is spanned over `B` by
the image of the universal derivation (`KaehlerDifferential.span_range_derivation`), and
`c ⊗ (b • ω) = (b • c) ⊗ ω`, so they do generate it once the `k`-action is allowed. -/
public theorem tensorKaehlerDifferential_ext {Λ B k M : Type u} [CommRing Λ] [CommRing B]
    [CommRing k] [Algebra Λ B] [Algebra B k] [Algebra Λ k] [AddCommGroup M] [Module k M]
    (f g : TensorProduct B k (KaehlerDifferential Λ B) →ₗ[k] M)
    (h : ∀ (c : k) (b : B), f (c ⊗ₜ[B] KaehlerDifferential.D Λ B b) =
      g (c ⊗ₜ[B] KaehlerDifferential.D Λ B b)) :
    f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul c ω =>
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D Λ B)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction generalizing c with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact h c b
    | zero => simp
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
    | smul b y _ hy => rw [← TensorProduct.smul_tmul]; exact hy (b • c)

/-! ### The base-change map of differentials on generators -/

section Tower

variable (Λ B A k : Type u) [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
  [Algebra Λ B] [Algebra Λ A] [Algebra Λ k] [Algebra B A] [Algebra B k] [Algebra A k]
  [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]

/-- The base-change map of differentials of a tower `Λ → B → A → k` sends `c ⊗ d b` to
`c ⊗ d (b mod B)`. -/
public theorem differentialsBaseChangeMap_tmul_D (c : k) (b : B) :
    differentialsBaseChangeMap Λ B A k (c ⊗ₜ[B] KaehlerDifferential.D Λ B b) =
      c ⊗ₜ[A] KaehlerDifferential.D Λ A (algebraMap B A b) := by
  change (KaehlerDifferential.mapBaseChange Λ B A).baseChange k
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange B A k k
        (KaehlerDifferential Λ B)).symm (c ⊗ₜ[B] KaehlerDifferential.D Λ B b)) = _
  have hsymm : (TensorProduct.AlgebraTensorModule.cancelBaseChange B A k k
      (KaehlerDifferential Λ B)).symm (c ⊗ₜ[B] KaehlerDifferential.D Λ B b) =
      c ⊗ₜ[A] ((1 : A) ⊗ₜ[B] KaehlerDifferential.D Λ B b) := by
    rw [LinearEquiv.symm_apply_eq,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [hsymm, LinearMap.baseChange_tmul, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D]

/-- **The identification.** For a tower `Λ → B → A → k` whose two maps onto `k` are
surjective, the base-change map of differentials of Stacks 07YL is the map on cotangent spaces
of the two presentations of `k` over `Λ` which Stacks 06H0 is stated with. -/
public theorem differentialsBaseChangeMap_eq_cotangentSpaceMap
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k)) :
    differentialsBaseChangeMap Λ B A k =
      Algebra.Extension.CotangentSpace.map (residueExtensionHom (Λ := Λ) hB hA) := by
  refine tensorKaehlerDifferential_ext _ _ fun c b => ?_
  rw [differentialsBaseChangeMap_tmul_D]
  refine (Eq.trans (Algebra.Extension.CotangentSpace.map_tmul
    (residueExtensionHom (Λ := Λ) hB hA) c b) ?_).symm
  rfl

end Tower

/-! ### Functoriality in the tower -/

/-- The base-change maps of differentials of two towers compose to the base-change map of the
composite tower. -/
@[ega "0 20.6.16" "more general"]
public theorem differentialsBaseChangeMap_comp (Λ A₂ A₁ A₀ k : Type u) [CommRing Λ]
    [CommRing A₂] [CommRing A₁] [CommRing A₀] [CommRing k]
    [Algebra Λ A₂] [Algebra Λ A₁] [Algebra Λ A₀] [Algebra Λ k]
    [Algebra A₂ A₁] [Algebra A₁ A₀] [Algebra A₂ A₀]
    [Algebra A₂ k] [Algebra A₁ k] [Algebra A₀ k]
    [IsScalarTower Λ A₂ A₁] [IsScalarTower Λ A₁ A₀] [IsScalarTower Λ A₂ A₀]
    [IsScalarTower A₂ A₁ A₀]
    [IsScalarTower Λ A₂ k] [IsScalarTower Λ A₁ k] [IsScalarTower Λ A₀ k]
    [IsScalarTower A₂ A₁ k] [IsScalarTower A₁ A₀ k] [IsScalarTower A₂ A₀ k] :
    (differentialsBaseChangeMap Λ A₁ A₀ k) ∘ₗ (differentialsBaseChangeMap Λ A₂ A₁ k) =
      differentialsBaseChangeMap Λ A₂ A₀ k := by
  refine tensorKaehlerDifferential_ext _ _ fun c b => ?_
  rw [LinearMap.comp_apply, differentialsBaseChangeMap_tmul_D,
    differentialsBaseChangeMap_tmul_D, differentialsBaseChangeMap_tmul_D,
    IsScalarTower.algebraMap_apply A₂ A₁ A₀ b]

end Deformation.Artin

namespace Deformation.ArtinianLocalAlgCat

open CategoryTheory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks 06H0, part (2), conditions (a) and (c)**, with the cotangent space written as the
base-change map of differentials. A morphism `f : B ⟶ A` of `𝒞_Λ` is an essential surjection
exactly when the canonical map `k ⊗_B Ω_{B/Λ} ⟶ k ⊗_A Ω_{A/Λ}` is bijective.

This is
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_cotangentSpaceMap_bijective`
composed with `Deformation.Artin.differentialsBaseChangeMap_eq_cotangentSpaceMap`. It is the
form in which the criterion meets Stacks 07YL, which produces its square-zero extension
together with the bijectivity of exactly this map. -/
@[stacks 06H0 "part (2), conditions (a) and (c), through the base-change map of differentials"]
public theorem isEssentialSurjection_iff_bijective_differentialsBaseChangeMap
    {B A : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : B ⟶ A) :
    letI : Algebra (B : Type u) (A : Type u) := f.hom.toRingHom.toAlgebra
    letI : IsScalarTower Λ (B : Type u) (A : Type u) :=
      .of_algebraMap_eq fun x => (f.hom.commutes x).symm
    letI : IsScalarTower (B : Type u) (A : Type u) k :=
      .of_algebraMap_eq fun b => (f.residue_comm b).symm
    (IsEssentialSurjection f ↔
      Function.Bijective
        (Deformation.Artin.differentialsBaseChangeMap Λ (B : Type u) (A : Type u) k)) := by
  let : Algebra (B : Type u) (A : Type u) := f.hom.toRingHom.toAlgebra
  let : IsScalarTower Λ (B : Type u) (A : Type u) :=
    .of_algebraMap_eq fun x => (f.hom.commutes x).symm
  let : IsScalarTower (B : Type u) (A : Type u) k :=
    .of_algebraMap_eq fun b => (f.residue_comm b).symm
  rw [isEssentialSurjection_iff_cotangentSpaceMap_bijective f,
    Deformation.Artin.differentialsBaseChangeMap_eq_cotangentSpaceMap Λ _ _ k
      (algebraMap_residue_surjective B) (algebraMap_residue_surjective A)]
  rfl

end Deformation.ArtinianLocalAlgCat
