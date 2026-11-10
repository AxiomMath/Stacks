module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.EtaleModuleScalarSplitting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.MatrixContinuousModuleScalarSplitting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafRestrictScalarsNaturality

/-!
# The scalar splitting of a lisse matrix sheaf after a finite free extension of the coefficients

Let `ρ : Λ →+* Λ''` be a homomorphism of finite commutative rings with elements `β_i ∈ Λ''` and
coordinate maps `π_i : Λ'' → Λ` (a basis of `Λ''` over `Λ` with its coordinate functionals), and
`σ` a representation of `π₁(X, x̄)` on `Λ^m` with open kernel. The lisse sheaf of `Λ''`-modules of
`ρ ∘ σ`, read over `Λ`, splits as `e` copies of the lisse sheaf of `σ`, with multiplication by
`o ∈ Λ''` the matrix `(π_k(o β_i))_{ki}`
(`Stacks.EtaleCohomology.etaleModuleScalarSplitting_lisseEtaleSheaf`): restriction of scalars of
lisse sheaves is the lisse sheaf of the restricted module
(`Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsModuleIso`, natural by
`Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIso_hom_naturality`), on which the
coordinates and injections of `Stacks.EtaleCohomology.matrixContinuousModuleCoordHom` and
`Stacks.EtaleCohomology.matrixContinuousModuleBasisHom` split it.

This is the lisse input of the extension of the level isogeny of Laumon's comparison from `O_E` to
`O''` (step R3 of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.additive_lisseEtaleSheaf`.
* `Stacks.EtaleCohomology.etaleModuleScalarSplitting_lisseEtaleSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- Sheafification of sheaves of `Λ`-modules on the small étale site of Stacks 021B, pinned at
the universe of `Stacks.EtaleCohomology.lisseSheaf` (the universe-polymorphic instance otherwise
leaves a universe constraint unsolved). -/
local instance hasSheafify_smallEtale_moduleCat_scalarSplitting (B : BigEtaleSite.{u})
    (X : B.Scheme) (Λ : Type) [CommRing Λ] :
    HasSheafify (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} _ Λ

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **The lisse sheaf functor is additive**: it is the inverse of an equivalence followed by the
inclusion of a full subcategory and an equivalence. -/
theorem additive_lisseEtaleSheaf (Λ : Type) [CommRing Λ] [Finite Λ] :
    (lisseEtaleSheaf B X x Λ).Additive := by
  have : (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.Additive :=
    Equivalence.additive_functor' (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).symm
  have := Equivalence.additive_functor' (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ))
  dsimp only [lisseEtaleSheaf, lisseSheaf]
  infer_instance

variable {Λ Λ'' : Type} [CommRing Λ] [CommRing Λ''] [Finite Λ] [Finite Λ''] (ρ : Λ →+* Λ'')
  {e : ℕ} (β : Fin e → Λ'') (π : Fin e → Λ'' →+ Λ)
  (h₁ : ∀ i (c : Λ) (x : Λ''), π i (ρ c * x) = c * π i x)
  (h₂ : ∀ i j, π j (β i) = if i = j then 1 else 0) (h₃ : ∀ x : Λ'', ∑ i, ρ (π i x) * β i = x)
  {m : ℕ} {σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) Λ}
  (hσ : IsOpen (σ.ker : Set (EtaleFundamentalGroup X.1 x)))
  (hσ'' : IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp σ).ker :
    Set (EtaleFundamentalGroup X.1 x)))

include h₂ h₃ in
/-- **The scalar splitting of the lisse sheaf of `ρ ∘ σ` over that of `σ`**, with matrices
`c(o)_{ki} = π_k(o β_i)`. -/
theorem etaleModuleScalarSplitting_lisseEtaleSheaf :
    EtaleModuleScalarSplitting ρ (fun o k i => π k (o * β i))
      ((lisseEtaleSheaf B X x Λ'').obj (matrixContinuousModule.{u + 1, u + 1} Λ''
        ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ''))
      ((lisseEtaleSheaf B X x Λ).obj (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ))
      (fun k => (lisseEtaleSheafRestrictScalarsModuleIso B X x ρ _).hom ≫
        (lisseEtaleSheaf B X x Λ).map (matrixContinuousModuleCoordHom ρ π h₁ hσ hσ'' k))
      (fun i => (lisseEtaleSheaf B X x Λ).map (matrixContinuousModuleBasisHom ρ β hσ hσ'' i) ≫
        (lisseEtaleSheafRestrictScalarsModuleIso B X x ρ _).inv) := by
  have := additive_lisseEtaleSheaf B X x Λ
  let L := lisseEtaleSheaf B X x Λ
  let i₀ := lisseEtaleSheafRestrictScalarsModuleIso B X x ρ
    (matrixContinuousModule.{u + 1, u + 1} Λ'' ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ'')
  refine ⟨fun i j => ?_, ?_, fun o i => ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← L.map_comp, matrixContinuousModuleBasisHom_comp_coordHom ρ β π h₁ hσ hσ'' h₂ i j]
    split_ifs
    · exact L.map_id _
    · exact L.map_zero _ _
  · rw [show (∑ k, (i₀.hom ≫ L.map (matrixContinuousModuleCoordHom ρ π h₁ hσ hσ'' k)) ≫
        L.map (matrixContinuousModuleBasisHom ρ β hσ hσ'' k) ≫ i₀.inv) =
        i₀.hom ≫ L.map (∑ k, matrixContinuousModuleCoordHom ρ π h₁ hσ hσ'' k ≫
          matrixContinuousModuleBasisHom ρ β hσ hσ'' k) ≫ i₀.inv by
      rw [L.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [L.map_comp, Category.assoc],
      sum_matrixContinuousModuleCoordHom_comp_basisHom ρ β π h₁ hσ hσ'' h₃, L.map_id,
      Category.id_comp, Iso.hom_inv_id]
  · -- multiplication by `o` on the lisse sheaf is the lisse sheaf of multiplication by `o`
    have hnat := lisseEtaleSheafRestrictScalarsIso_hom_naturality ρ
      (finiteTypeContinuousModuleSMul Λ'' (matrixContinuousModule.{u + 1, u + 1} Λ''
        ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ'') o)
      (matrixContinuousModuleRestrictScalarsMulHom ρ hσ'' o) (Iso.refl _) (fun _ => rfl)
      (Iso.refl _) (fun _ => rfl) rfl
    have hinv : i₀.inv ≫ (etaleModuleRestrictScalars ρ X.1).map
        ((etaleModuleSMul X.1 o).app ((lisseEtaleSheaf B X x Λ'').obj
          (matrixContinuousModule.{u + 1, u + 1} Λ''
            ((Matrix.GeneralLinearGroup.map ρ).comp σ) hσ''))) =
        L.map (matrixContinuousModuleRestrictScalarsMulHom ρ hσ'' o) ≫ i₀.inv := by
      rw [etaleModuleSMul_app_lisseEtaleSheaf, Iso.inv_comp_eq, ← Category.assoc,
        Iso.eq_comp_inv]
      exact hnat
    rw [Category.assoc, hinv, ← Category.assoc, ← L.map_comp,
      matrixContinuousModuleBasisHom_comp_mulHom ρ β π hσ hσ'' h₃ o i, L.map_sum,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [L.map_comp, etaleModuleSMul_app_lisseEtaleSheaf, Category.assoc]

end Stacks.EtaleCohomology

end
