module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxGraded

/-!
# The dévissage of part (2) of [Stacks, Tag 0897], run over an auxiliary graded algebra

Let `𝓑 = ⨁ ℐᵐ/ℐᵐ⁺¹` be the associated graded algebra of an ideal sheaf on a scheme `X` proper
over a Noetherian ring, and let `φ : 𝓟 ⟶ 𝓑` be a unital homomorphism of sheaves of graded
algebras which is surjective on the sections over affine opens and whose homogeneous pieces have
finite sections over affine opens. If every quasi-coherent graded `𝓟`-module of finite type `M`
sits in degreewise short exact sequences `0 → R → P → M → 0` of graded `𝓟`-modules, with `R`
again quasi-coherent of finite type and with the twists of `P` acyclic in all positive degrees
uniformly in the homogeneous degree, then every quasi-coherent graded `𝓑`-module of finite type
has uniformly acyclic twists.

## Main definitions

* `Stacks.Coherent.gradedAppMod`: the degree-`n` component of a homomorphism of graded modules,
  as a morphism of `𝒪_X`-modules.
* `Stacks.Coherent.kerShortComplex`: the degreewise short complex `0 → (ker π)ₙ → Qₙ → Nₙ → 0` of
  a homomorphism `π : Q ⟶ N` of graded modules, with the graded kernel
  `SheafOfModules.GradedModule.ker` as its first term.

## Main results

* `Stacks.Coherent.shortExact_kerShortComplex`: for a homomorphism of graded modules which is an
  epimorphism in every degree, the short complexes `Stacks.Coherent.kerShortComplex` are short
  exact.
* `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_devissage_over`: part (2) of
  [Stacks, Tag 0897] for the associated graded algebra, from a dévissage of graded `𝓟`-modules.
* `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over`: the same, from a
  degreewise epimorphism of graded `𝓟`-modules onto every quasi-coherent graded `𝓟`-module of
  finite type.
* `Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_presentation`: the hypothesis
  `Stacks.Coherent.HasAssociatedGradedTwistVanishing` of [Stacks, Tag 0884], from such a `𝓟`
  for each presentation `D` of the associated graded algebra.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace Stacks.Coherent

attribute [local instance] HasDerivedCategory.standard

/-! ### The dévissage short complexes of a graded epimorphism -/

section KerShortComplex

variable {X : Scheme.{u}} {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- The degree-`n` component of a homomorphism of graded modules, read as a morphism of
`𝒪_X`-modules. -/
public abbrev gradedAppMod {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N) (n : ℤ) :
    modPiece Q n ⟶ modPiece N n :=
  π.app n

/-- **The degreewise dévissage short complex of a homomorphism of graded modules**
`0 → (ker π)ₙ → Qₙ → Nₙ → 0`, with the graded kernel
`SheafOfModules.GradedModule.ker` as its first term. -/
public def kerShortComplex {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N) (n : ℤ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (gradedAppMod (SheafOfModules.GradedModule.kerι π) n) (gradedAppMod π n)
    (SheafOfModules.GradedModule.comp_eq_zero_app
      (SheafOfModules.GradedModule.kerι_comp π) n)

/-- The first term of `kerShortComplex π n` is the degree-`n` piece of the graded kernel of
`π`. -/
@[simp] theorem kerShortComplex_X₁ {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N) (n : ℤ) :
    (kerShortComplex π n).X₁ = (SheafOfModules.GradedModule.ker π).piece n := rfl

/-- The second term of `kerShortComplex π n` is the degree-`n` piece of the source of `π`. -/
@[simp] theorem kerShortComplex_X₂ {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N) (n : ℤ) :
    (kerShortComplex π n).X₂ = Q.piece n := rfl

/-- The third term of `kerShortComplex π n` is the degree-`n` piece of the target of `π`. -/
@[simp] theorem kerShortComplex_X₃ {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N) (n : ℤ) :
    (kerShortComplex π n).X₃ = N.piece n := rfl

/-- **A degreewise epimorphism of graded modules has degreewise short exact kernel sequences.**
If `π` is an epimorphism in every degree, then `kerShortComplex π n` is short exact. -/
public theorem shortExact_kerShortComplex {Q N : SheafOfModules.GradedModule P} (π : Q ⟶ N)
    (hepi : ∀ n : ℤ, Epi (gradedAppMod π n)) (n : ℤ) :
    (kerShortComplex π n).ShortExact := by
  have := hepi n
  have : Mono (kerShortComplex π n).f :=
    inferInstanceAs (Mono (SheafOfModules.kerIota (π.app n)))
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (SheafOfModules.kerIsLimit (π.app n)))
    inferInstance (hepi n)

end KerShortComplex

/-! ### The dévissage, run over an auxiliary graded algebra -/

/-- **Part (2) of [Stacks, Tag 0897] for the associated graded algebra of an ideal sheaf, from a
dévissage of graded modules over an auxiliary graded algebra.**

Let `A` be Noetherian, `f : X ⟶ Spec A` proper, `L` an invertible `𝒪_X`-module, let `D` present
the associated graded algebra `𝓑` of an ideal sheaf of `X`, and let `φ : 𝓟 ⟶ 𝓑` be a unital
homomorphism of sheaves of graded algebras which

* `hφ` is surjective on the sections over affine opens, in every degree, and
* `hPfin` has homogeneous pieces whose sections over affine opens are finite modules.

Assume every quasi-coherent graded `𝓟`-module of finite type on affine opens fits, in every
positive cohomological degree, in a degreewise short exact sequence `0 → R → P → M → 0` with `R`
again quasi-coherent of finite type and with the twists of `P` acyclic in all positive degrees
for all large `d`, uniformly in the homogeneous degree. Then every quasi-coherent graded
`𝓑`-module of finite type has uniformly acyclic twists: one `d₀` serves every positive
cohomological degree and every homogeneous degree. -/
public theorem exists_isZero_Hgroup_piece_tensorPowModule_of_devissage_over
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
    {I : X.IdealSheafData} {D : AssociatedGradedAlgebraData I}
    {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (φ : SheafOfModules.GradedAlgebra.UnitalHom P D.algebra)
    (hφ : ∀ (U : X.affineOpens) (i : ℤ) (b : (D.algebra.piece i).val.obj (op U.1)),
      ∃ a : (P.piece i).val.obj (op U.1), (φ.app i).val.app (op U.1) a = b)
    (hPfin : ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1))
    (hdev : ∀ N : SheafOfModules.GradedModule P,
      (∀ n : ℤ, (N.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine N → ∀ p : ℕ, 0 < p →
      ∃ (R : SheafOfModules.GradedModule P) (S : ℤ → ShortComplex X.Modules),
        (∀ n : ℤ, (S n).ShortExact) ∧
        (∀ n : ℤ, (S n).X₁ = R.piece n) ∧ (∀ n : ℤ, (S n).X₃ = N.piece n) ∧
        (∀ n : ℤ, (R.piece n).IsQuasicoherent) ∧ IsFiniteTypeOnAffine R ∧
        ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
          IsZero (Hgroup X.ringCatSheaf ⊤ m
            (tensorModules X (S n).X₂ (tensorPowModule X L d))))
    (M : SheafOfModules.GradedModule D.algebra)
    (hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (M.piece n) (tensorPowModule X L d))) :=
  exists_isZero_Hgroup_piece_tensorPowModule_of_devissage A f L hPfin hdev
    (M.restrictScalars φ) hqc (isFiniteTypeOnAffine_restrictScalars φ hφ M hft)

/-- **Part (2) of [Stacks, Tag 0897] from a presentation of graded `𝓟`-modules by graded
epimorphisms.**

The same as `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_devissage_over`, with
the family of degreewise short exact sequences replaced by what produces it: a homomorphism of
graded `𝓟`-modules `π : Q ⟶ N` which is an epimorphism in every degree, whose source has
uniformly acyclic twists and whose graded kernel is quasi-coherent of finite type. -/
public theorem exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
    {I : X.IdealSheafData} {D : AssociatedGradedAlgebraData I}
    {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (φ : SheafOfModules.GradedAlgebra.UnitalHom P D.algebra)
    (hφ : ∀ (U : X.affineOpens) (i : ℤ) (b : (D.algebra.piece i).val.obj (op U.1)),
      ∃ a : (P.piece i).val.obj (op U.1), (φ.app i).val.app (op U.1) a = b)
    (hPfin : ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1))
    (hepi : ∀ N : SheafOfModules.GradedModule P,
      (∀ n : ℤ, (N.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine N → ∀ p : ℕ, 0 < p →
      ∃ (Q : SheafOfModules.GradedModule P) (π : Q ⟶ N),
        (∀ n : ℤ, Epi (gradedAppMod π n)) ∧
        (∀ n : ℤ, ((SheafOfModules.GradedModule.ker π).piece n).IsQuasicoherent) ∧
        IsFiniteTypeOnAffine (SheafOfModules.GradedModule.ker π) ∧
        ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
          IsZero (Hgroup X.ringCatSheaf ⊤ m
            (tensorModules X (Q.piece n) (tensorPowModule X L d))))
    (M : SheafOfModules.GradedModule D.algebra)
    (hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (M.piece n) (tensorPowModule X L d))) := by
  refine exists_isZero_Hgroup_piece_tensorPowModule_of_devissage_over A f L φ hφ hPfin
    (fun N hNqc hNft p hp => ?_) M hqc hft
  obtain ⟨Q, π, hπ, hKqc, hKft, d₁, hd₁⟩ := hepi N hNqc hNft p hp
  exact ⟨SheafOfModules.GradedModule.ker π, kerShortComplex π,
    fun n => shortExact_kerShortComplex π hπ n, fun _ => rfl, fun _ => rfl, hKqc, hKft, d₁, hd₁⟩

/-- **The hypothesis of [Stacks, Tag 0884] from a presentation of the associated graded algebra
by a graded algebra with finite pieces.**

`Stacks.Coherent.HasAssociatedGradedTwistVanishing`, part (2) of [Stacks, Tag 0897] for the
associated graded algebra of `I · 𝒪_X`, holds as soon as, for `L` ample, every presentation `D`
of that algebra is the target of a unital homomorphism `φ : 𝓟 ⟶ D.algebra` which is surjective
on affine sections, whose source has pieces finite over affine opens, and over whose graded
modules every quasi-coherent graded module of finite type is the target of a degreewise
epimorphism with quasi-coherent kernel of finite type and with source having uniformly acyclic
twists. -/
public theorem hasAssociatedGradedTwistVanishing_of_presentation
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L]
    (hpres : IsAmple X L → ∀ D : AssociatedGradedAlgebraData
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f),
      ∃ (P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
        (φ : SheafOfModules.GradedAlgebra.UnitalHom P D.algebra),
        (∀ (U : X.affineOpens) (i : ℤ) (b : (D.algebra.piece i).val.obj (op U.1)),
          ∃ a : (P.piece i).val.obj (op U.1), (φ.app i).val.app (op U.1) a = b) ∧
        (∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1)) ∧
        ∀ N : SheafOfModules.GradedModule P,
          (∀ n : ℤ, (N.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine N → ∀ p : ℕ, 0 < p →
          ∃ (Q : SheafOfModules.GradedModule P) (π : Q ⟶ N),
            (∀ n : ℤ, Epi (gradedAppMod π n)) ∧
            (∀ n : ℤ, ((SheafOfModules.GradedModule.ker π).piece n).IsQuasicoherent) ∧
            IsFiniteTypeOnAffine (SheafOfModules.GradedModule.ker π) ∧
            ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → ∀ m : ℕ, 0 < m → ∀ n : ℤ,
              IsZero (Hgroup X.ringCatSheaf ⊤ m
                (tensorModules X (Q.piece n) (tensorPowModule X L d)))) :
    HasAssociatedGradedTwistVanishing A I f L := by
  intro hL D M hqc hft
  obtain ⟨P, φ, hφ, hPfin, hepi⟩ := hpres hL D
  exact exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over A f L (D := D) φ hφ hPfin
    hepi M hqc hft

end Stacks.Coherent

end
