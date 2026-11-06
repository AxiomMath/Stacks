module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.MatrixContinuousModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheafTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensorStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf

/-!
# The Fourier integrand of a lisse matrix sheaf is the lisse sheaf of the twist

Let `k'` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k'` with
values in `Λ` and `σ` a representation of `π₁(𝔸¹_x)` on `Λ^m` with open kernel. On Laumon's
plane `Spec k'[x][t]`, with first projection `pr₁`, the integrand `pr₁⁻¹ ℱ_σ ⊗ L_ψ(x t)` of the
Fourier transform of the lisse sheaf `ℱ_σ` is the lisse sheaf of the twist
`pr₁^* σ ⊗ ψ(-χ_{x t})`: the inverse image of a lisse sheaf is the lisse sheaf of the restricted
module (Tag 0DV6), and the tensor product of the lisse sheaves of `Λ^m` and of a character is the
lisse sheaf of the twisted action, the pairing `(v, a) ↦ a v` being equivariant and onto with
`Λ^m ⊗ Λ ≅ Λ^m`.

## Main results

* `lisseEtaleSheafMatrixTensorCharacterIso`: `ℱ_{Λ^m, σ} ⊗ ℱ_χ ≅ ℱ_{Λ^m, σ ⊗ χ}`.
* `nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso`:
  `pr₁⁻¹ ℱ_σ ⊗ L_ψ(x t) ≅ ℱ_{pr₁^* σ ⊗ ψ(-χ_{x t})}` on `Spec k'[x][t]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.GroupCohomology
  Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-- Sheafification of étale sheaves of `Λ`-modules, at the universes of `EtaleModules.{u, 0}`
(pinned, so that the monoidal structure does not leave a universe metavariable). -/
local instance hasSheafify_etaleModules_laumonKernelTwist (Λ : Type) [CommRing Λ]
    (X : Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasSheafifyEtale X Λ

section Twist

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ] {m : ℕ}

/-- The pairing `Λ^m × Λ → Λ^m`, `(v, a) ↦ a v`, on the carriers of the matrix and character
modules. -/
def matrixCharacterSMulBilinear :
    ULift.{u + 1} (Fin m → Λ) →ₗ[Λ] ULift.{u + 1} Λ →ₗ[Λ] ULift.{u + 1} (Fin m → Λ) :=
  LinearMap.mk₂ Λ (fun v a => ULift.up (a.down • v.down))
    (fun v₁ v₂ a => ULift.ext (smul_add a.down v₁.down v₂.down))
    (fun c v a => ULift.ext (smul_comm a.down c v.down))
    (fun v a₁ a₂ => ULift.ext (add_smul a₁.down a₂.down v.down))
    (fun c v a => ULift.ext (mul_smul c a.down v.down))

variable {Λ} in
omit [Finite Λ] in
/-- The pairing `(v, a) ↦ a v` is equivariant from `Λ^m_σ × Λ_χ` to `Λ^m_{σ ⊗ χ}`. -/
theorem matrixCharacterSMulBilinear_equivariant
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup X.1 x)))
    (χ : EtaleFundamentalGroup X.1 x →* Λˣ)
    (hχ : IsOpen (χ.ker : Set (EtaleFundamentalGroup X.1 x)))
    (hσχ : IsOpen ((characterTwist σ χ).ker : Set (EtaleFundamentalGroup X.1 x)))
    (g : EtaleFundamentalGroup X.1 x)
    (a : (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ).obj.obj.obj.V)
    (b : (characterContinuousModule Λ χ hχ).obj.obj.obj.V) :
    matrixCharacterSMulBilinear Λ
        (((matrixContinuousModule.{u + 1, u + 1} Λ σ hσ).obj.obj.obj.ρ g).asHom.hom a)
        (((characterContinuousModule Λ χ hχ).obj.obj.obj.ρ g).asHom.hom b) =
      ((matrixContinuousModule.{u + 1, u + 1} Λ (characterTwist σ χ) hσχ).obj.obj.obj.ρ g).asHom.hom
        (matrixCharacterSMulBilinear Λ a b) := by
  refine ULift.ext ?_
  have hs : ∀ w : Fin m → Λ, Matrix.scalar (Fin m) (χ g : Λ) *ᵥ w = (χ g : Λ) • w := fun w => by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  show ((χ g : Λ) • b.down) • ((σ g).val *ᵥ a.down) =
    ((σ g).val * Matrix.scalar (Fin m) (χ g : Λ)) *ᵥ (b.down • a.down)
  rw [← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_eq_mul, mul_smul]

/-- **`ℱ_{Λ^m, σ} ⊗ ℱ_χ ≅ ℱ_{Λ^m, σ ⊗ χ}`**: the tensor product of the lisse sheaves of a matrix
representation and of a character is the lisse sheaf of the twisted representation; the pairing
`(v, a) ↦ a v` is equivariant and onto, and `Λ^m ⊗ Λ ≅ Λ^m`. -/
def lisseEtaleSheafMatrixTensorCharacterIso
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup X.1 x)))
    (χ : EtaleFundamentalGroup X.1 x →* Λˣ)
    (hχ : IsOpen (χ.ker : Set (EtaleFundamentalGroup X.1 x)))
    (hσχ : IsOpen ((characterTwist σ χ).ker : Set (EtaleFundamentalGroup X.1 x))) :
    (lisseEtaleSheaf B X x Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ) ⊗
        (lisseEtaleSheaf B X x Λ).obj (characterContinuousModule Λ χ hχ) ≅
      (lisseEtaleSheaf B X x Λ).obj
        (matrixContinuousModule.{u + 1, u + 1} Λ (characterTwist σ χ) hσχ) :=
  have hsurj :
      ∀ r : (matrixContinuousModule.{u + 1, u + 1} Λ (characterTwist σ χ) hσχ).obj.obj.obj.V,
        ∃ p q, matrixCharacterSMulBilinear Λ p q = r :=
    fun r => ⟨r, ULift.up 1, ULift.ext (one_smul Λ r.down)⟩
  have hcard : Nat.card (TensorProduct Λ
      (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ).obj.obj.obj.V
      (characterContinuousModule Λ χ hχ).obj.obj.obj.V) ≤
      Nat.card (matrixContinuousModule.{u + 1, u + 1} Λ (characterTwist σ χ) hσχ).obj.obj.obj.V :=
    (Nat.card_congr ((TensorProduct.congr (LinearEquiv.refl Λ (ULift.{u + 1} (Fin m → Λ)))
      (ULift.moduleEquiv (R := Λ))).trans (TensorProduct.rid Λ _)).toEquiv).le
  haveI := isIso_lisseEtaleSheafTensorHom B X x Λ
    (P := matrixContinuousModule.{u + 1, u + 1} Λ σ hσ)
    (Q := characterContinuousModule Λ χ hχ)
    (R := matrixContinuousModule.{u + 1, u + 1} Λ (characterTwist σ χ) hσχ)
    (matrixCharacterSMulBilinear Λ)
    (matrixCharacterSMulBilinear_equivariant B X x σ hσ χ hχ hσχ) hsurj hcard
  asIso (lisseEtaleSheafTensorHom B X x Λ (matrixCharacterSMulBilinear Λ)
    (matrixCharacterSMulBilinear_equivariant B X x σ hσ χ hχ hσχ))

/-- The matrix module of `σ` restricted along a continuous homomorphism `φ` is the matrix module
of `σ ∘ φ`. -/
def finiteTypeContinuousModuleResMatrixIso {G : Type (u + 1)} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : EtaleFundamentalGroup X.1 x →ₜ* G)
    (σ : G →* GL (Fin m) Λ) (hσ : IsOpen (σ.ker : Set G))
    (hσφ : IsOpen ((σ.comp φ.toMonoidHom).ker : Set (EtaleFundamentalGroup X.1 x))) :
    (finiteTypeContinuousModuleRes Λ φ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ) ≅
      matrixContinuousModule.{u + 1, u + 1} Λ (σ.comp φ.toMonoidHom) hσφ :=
  finiteTypeContinuousModuleIsoOfLinearEquiv Λ (LinearEquiv.refl Λ _) fun _ _ => rfl

end Twist

section Laumon

variable (k' : Type u) [Field k'] [Fintype k'] (Λ : Type) [CommRing Λ] [Finite Λ]
  (ψ : AddChar k' Λ) (B : BigEtaleSite.{u})

/-- **The Fourier integrand of a lisse matrix sheaf on Laumon's plane**:
`pr₁⁻¹ ℱ_σ ⊗ L_ψ(x t) ≅ ℱ_{pr₁^* σ ⊗ ψ(-χ_{x t})}` on `Spec k'[x][t]`, for a representation `σ` of
`π₁(𝔸¹_x)` on `Λ^m` with open kernel. -/
theorem nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (pK : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k'))
        (Polynomial.C Polynomial.X * Polynomial.X))) {m : ℕ}
    (σ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    (hσ' : IsOpen ((characterTwist
      (σ.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
      (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
        (Polynomial.C Polynomial.X * Polynomial.X) ψ z pK)).ker :
          Set (EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (laumonFamilyPr₁ k')).obj
        ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
          (z.map (laumonFamilyPr₁ k')) Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ)) ⊗
        Stacks.ArtinSchreier.artinSchreierLevelSheaf k' (Polynomial (Polynomial k'))
          (Polynomial.C Polynomial.X * Polynomial.X) Λ ψ B hS z pK ≅
      (lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) z
        Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ _ hσ')) := by
  let Y := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  let X := Stacks.ArtinSchreier.specObject (Polynomial k') B hL
  have : ConnectedSpace X.1 := inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial k'))))
  have : ConnectedSpace Y.1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial (Polynomial k')))))
  let f : Y ⟶ X := ObjectProperty.homMk (laumonFamilyPr₁ k')
  let φ := etaleFundamentalGroupMap (laumonFamilyPr₁ k') z
  have hσφ : IsOpen ((σ.comp φ.toMonoidHom).ker : Set (EtaleFundamentalGroup Y.1 z)) :=
    hσ.preimage φ.continuous
  obtain ⟨a⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B f z Λ
    (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ)
  let c := lisseEtaleSheafMatrixTensorCharacterIso B Y z Λ
    (σ.comp φ.toMonoidHom) hσφ
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (Polynomial.C Polynomial.X * Polynomial.X) ψ z pK)
    (Stacks.ArtinSchreier.isOpen_ker_artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (Polynomial.C Polynomial.X * Polynomial.X) Λ ψ z pK) hσ'
  exact ⟨((a ≪≫ (lisseEtaleSheaf B Y z Λ).mapIso
      (finiteTypeContinuousModuleResMatrixIso B Y z Λ φ σ hσ hσφ)) ⊗ᵢ Iso.refl _) ≪≫ c⟩

end Laumon

end Stacks.EtaleCohomology

end
