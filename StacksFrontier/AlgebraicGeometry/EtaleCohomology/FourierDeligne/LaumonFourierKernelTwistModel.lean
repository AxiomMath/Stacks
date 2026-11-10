module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierTransformComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierKernelTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCharacterAdd
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelProduct
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily

/-!
# The Fourier integrand of an `O_E`-model and its reductions

On Laumon's plane `Spec k'[x][t]`, the Fourier integrand of `ℱ_{σ'}` for a representation `σ'` of
`π₁(𝔸¹_x)` is the lisse sheaf of the twist `pr₁^* σ' ⊗ ψ(-χ_{x t})`; see
`Stacks.EtaleCohomology.nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso`.
For an `O_E`-model `σ_O` of `σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` this file records:

* the twist commutes with reduction of the coefficients
  (`Stacks.EtaleCohomology.map_comp_characterTwist`,
  `Stacks.ArtinSchreier.artinSchreierCharacter_compAddChar`), and the reductions of the twist of
  `σ_O` modulo every `ℓᵏ` have open kernel;
* the twist `pr₁^* σ_O ⊗ ψ_O(-χ_{x t})` is an `O_E`-model of the Fourier family representation
  `pr₁^* σ₁ ⊗ ψ'(-χ_{a xⁿ + x t})` (`Stacks.EtaleCohomology.laumonFourierFamilyRep`), conjugated by
  the same matrix as `σ_O` (`Stacks.EtaleCohomology.map_laumonFourierTwistModel`): the
  Artin–Schreier characters of `a xⁿ` and `x t` multiply to that of `a xⁿ + x t`;
* `H¹` of the Fourier transform of `ℱ_σ` is `R¹pr₂!` of the lisse sheaf of the twist
  (`Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_lowerShriekHomology_lisse`, from
  pieces P2 and P2b).

These are the Fourier side of the level isogeny of piece L6 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.laumonFourierTwistModel`.

## Main results

* `Stacks.EtaleCohomology.isOpen_ker_characterTwist`.
* `Stacks.EtaleCohomology.isOpen_ker_map_laumonFourierTwistModel`.
* `Stacks.EtaleCohomology.map_laumonFourierTwistModel`.
* `Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_lowerShriekHomology_lisse`.

## Implementation notes

The Fourier transform and `R¹pr₂!` live in the standard model `HasDerivedCategory.standard` of
the derived category, which is a local instance in the last section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Matrix Polynomial

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))] {O O' : Type} [CommRing O] [CommRing O'] (f : O →+* O')
  (ψ : AddChar k O)

/-- **The Artin–Schreier character of `f ∘ ψ` is `f` applied to that of `ψ`.** -/
theorem artinSchreierCharacter_compAddChar (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    artinSchreierCharacter k A g (f.toMonoidHom.compAddChar ψ) x p₀ =
      (Units.map f.toMonoidHom).comp (artinSchreierCharacter k A g ψ x p₀) := by
  ext σ
  rfl

end Stacks.ArtinSchreier

namespace Stacks.EtaleCohomology

section Twist

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n] {O O' : Type}
  [CommRing O] [CommRing O']

/-- **Reducing the coefficients of a twist** is twisting the reduction by the reduced character. -/
theorem map_comp_characterTwist (f : O →+* O') (ρ : G →* GL n O) (χ : G →* Oˣ) :
    (Matrix.GeneralLinearGroup.map f).comp (characterTwist ρ χ) =
      characterTwist ((Matrix.GeneralLinearGroup.map f).comp ρ)
        ((Units.map f.toMonoidHom).comp χ) := by
  ext g i j
  change f ((characterTwist ρ χ g).val i j) = (characterTwist _ _ g).val i j
  rw [characterTwist_val, characterTwist_val]
  simp [Matrix.smul_apply]

/-- **The kernel of a twist is open** when those of the representation and of the character
are. -/
theorem isOpen_ker_characterTwist [TopologicalSpace G] [IsTopologicalGroup G] (ρ : G →* GL n O)
    (χ : G →* Oˣ) (hρ : IsOpen (ρ.ker : Set G)) (hχ : IsOpen (χ.ker : Set G)) :
    IsOpen ((characterTwist ρ χ).ker : Set G) := by
  refine Subgroup.isOpen_mono (H₁ := ρ.ker ⊓ χ.ker) (fun g hg => ?_) (hρ.inter hχ)
  rw [MonoidHom.mem_ker]
  ext : 1
  rw [characterTwist_val, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2]
  simp

end Twist

section Model

attribute [local instance] padicIntAlgebraOfRat

variable (k' : Type u) [Field k'] [Fintype k'] {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E]
  [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (ψ' : AddChar k' E)
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (pK : (finiteEtaleFiberFunctor z).obj (Stacks.ArtinSchreier.cover k'
    (Polynomial (Polynomial k')) (Polynomial.C Polynomial.X * Polynomial.X))) {m : ℕ}
  (σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
    GL (Fin m) (integralClosure ℤ_[ℓ] E))

/-- **The twist `pr₁^* σ_O ⊗ ψ_O(-χ_{x t})` of an `O_E`-representation of `π₁(𝔸¹_x)`**, a
representation of `π₁(Spec k'[x][t])` over `O_E`, `ψ_O` being `ψ'` with values in `O_E`. -/
def laumonFourierTwistModel :
    EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z →*
      GL (Fin m) (integralClosure ℤ_[ℓ] E) :=
  characterTwist (σO.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (Polynomial.C Polynomial.X * Polynomial.X) (padicIntegerRingAddChar ψ') z pK)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The reductions of the twist** are the twists of the reductions by the reduced characters. -/
theorem map_comp_laumonFourierTwistModel (k : ℕ) :
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp
        (laumonFourierTwistModel k' ψ' z pK σO) =
      characterTwist (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
        (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp σO).comp
          (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
          (Polynomial.C Polynomial.X * Polynomial.X)
          ((Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k})).toMonoidHom.compAddChar
            (padicIntegerRingAddChar ψ')) z pK) := by
  rw [laumonFourierTwistModel, map_comp_characterTwist,
    Stacks.ArtinSchreier.artinSchreierCharacter_compAddChar]
  rfl

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The reductions of the twist modulo every `ℓᵏ` have open kernel**, as soon as those of `σ_O`
have. -/
theorem isOpen_ker_map_laumonFourierTwistModel
    (hσO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp σO).ker :
        Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
    (k : ℕ) :
    IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp
        (laumonFourierTwistModel k' ψ' z pK σO)).ker :
      Set (EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z)) := by
  rw [map_comp_laumonFourierTwistModel]
  refine isOpen_ker_characterTwist _ _ ?_
    (Stacks.ArtinSchreier.isOpen_ker_artinSchreierCharacter k' (Polynomial (Polynomial k'))
      _ _ _ z pK)
  rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact (hσO k).preimage (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).continuous

variable (n : ℕ) (a : k')
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
  (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
    GL (Fin m) E)
  (p₁ : (finiteEtaleFiberFunctor (z.map (laumonFamilyPr₁ k'))).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n)))

/-- **The Artin–Schreier character of the Fourier kernel `a xⁿ + x t`** is the product of the
pull-back of that of `a xⁿ` along `pr₁` and that of `x t`. -/
theorem artinSchreierCharacter_laumonFourierKernel :
    Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
        (laumonFourierKernel k' n a) ψ' z p₀ =
      (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k')) p₁).comp
          (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom *
        Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
          (Polynomial.C Polynomial.X * Polynomial.X) ψ' z pK := by
  let φ : Polynomial k' →ₐ[k'] Polynomial (Polynomial k') := Polynomial.CAlgHom
  obtain ⟨q⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (φ (Polynomial.C a * Polynomial.X ^ n)) z
  have hmap := Stacks.ArtinSchreier.artinSchreierCharacter_map k'
    (Polynomial.C a * Polynomial.X ^ n) φ ψ' z q p₁
  have hadd : Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
        (laumonFourierKernel k' n a) ψ' z p₀ =
      Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
          (φ (Polynomial.C a * Polynomial.X ^ n)) ψ' z q *
        Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
          (Polynomial.C Polynomial.X * Polynomial.X) ψ' z pK :=
    Stacks.ArtinSchreier.artinSchreierCharacter_add ψ' z q pK p₀
  rw [hadd, hmap]
  rfl

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The twist of an `O_E`-model of `σ₁ ⊗ L_{ψ'}(a xⁿ)` is an `O_E`-model of the Fourier family
representation**, conjugated by the same matrix. -/
theorem map_laumonFourierTwistModel (T₁ : GL (Fin m) E)
    (hT₁ : ∀ g, (σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
      (T₁⁻¹ : GL (Fin m) E).val * (characterTwist σ₁ (Stacks.ArtinSchreier.artinSchreierCharacter
        k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k'))
          p₁) g).val * T₁.val)
    (g : EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z) :
    (laumonFourierTwistModel k' ψ' z pK σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
      (T₁⁻¹ : GL (Fin m) E).val * (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁ g).val * T₁.val := by
  rw [laumonFourierTwistModel, laumonFourierFamilyRep, characterTwist_val, characterTwist_val,
    Matrix.map_smul' _ _ _ (map_mul _), MonoidHom.comp_apply, hT₁, characterTwist_val,
    artinSchreierCharacter_laumonFourierKernel k' ψ' z pK n a p₀ p₁, MonoidHom.mul_apply,
    Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    MonoidHom.comp_apply]
  congr 1
  rw [mul_comm]
  rfl

end Model

section Fourier

attribute [local instance] HasDerivedCategory.standard

variable (k' : Type u) [Field k'] [Fintype k'] (Λ : Type) [CommRing Λ] [Finite Λ]
  (ψ : AddChar k' Λ) (B : BigEtaleSite.{u})

/-- **`H¹` of the Fourier transform of a lisse matrix sheaf is `R¹pr₂!` of the lisse sheaf of the
twist** `pr₁^* σ ⊗ ψ(-χ_{x t})` on Laumon's plane (pieces P2 and P2b), for any representation `τ`
equal to the twist. -/
theorem nonempty_homology_fourierTransform_iso_lowerShriekHomology_lisse
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
    (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (pK : (finiteEtaleFiberFunctor z).obj (Stacks.ArtinSchreier.cover k'
      (Polynomial (Polynomial k')) (Polynomial.C Polynomial.X * Polynomial.X))) {m : ℕ}
    (σ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial k')))
      (z.map (laumonFamilyPr₁ k')))))
    (τ : EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z →* GL (Fin m) Λ)
    (hτ : IsOpen (τ.ker : Set (EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z)))
    (hστ : characterTwist (σ.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
      (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
        (Polynomial.C Polynomial.X * Polynomial.X) ψ z pK) = τ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((fourierTransform k' Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
            (z.map (laumonFamilyPr₁ k')) Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ)))) ≅
      (lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1).obj
        ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) z
          Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ τ hτ))) := by
  subst hστ
  obtain ⟨e₁⟩ := nonempty_homology_fourierTransform_iso_laumonFamily k' Λ ψ B p₀ j hS hL jg z pK
    ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (z.map (laumonFamilyPr₁ k')) Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ))
  obtain ⟨e₂⟩ := nonempty_inverseImage_lisseEtaleSheaf_tensor_artinSchreierLevelSheaf_iso k' Λ ψ B
    hS hL z pK σ hσ hτ
  exact ⟨e₁ ≪≫ (lowerShriekHomology Λ (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg
    1).mapIso e₂⟩

end Fourier

end Stacks.EtaleCohomology

end
