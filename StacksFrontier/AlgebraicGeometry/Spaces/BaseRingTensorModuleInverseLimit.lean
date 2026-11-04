module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseLimitSequenceEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent

/-!
# The two rows of the proof of Stacks 0D3F

Let `X` be an algebraic space, `R` a ring with a ring map to `Γ(X, 𝒪_X)` and `(M_n)` a tower of
`R`-modules with surjective transition maps.  The proof of Stacks 0D3F compares the image under
`Φ = 𝒪_X ⊗_R -` of the short exact sequence `lim M_n ⟶ ∏ M_n ⟶ ∏ M_n` with the sequence
`lim Φ(M_n) ⟶ ∏ Φ(M_n) ⟶ ∏ Φ(M_n)`; both have to be short exact.

* The second is short exact with no hypothesis on `X`: `Φ` carries the surjections `M_{n+1} ⟶ M_n`
  to epimorphisms of quasi-coherent modules, which are surjective on the sections over affine
  étale charts (Stacks 03DW), and those charts cover `X`.
* The first is short exact when `R = Γ(T, 𝒪_T)` for an affine `T` and `X ⟶ T` is flat: `Φ` is
  right exact, being a left adjoint, and it preserves injections by flatness.

## Main results

* `AlgebraicGeometry.Space.shortExact_inverseLimitSequence_baseRingTensorModule`: the second row.
* `AlgebraicGeometry.Space.shortExact_map_inverseLimitSequence_baseRingTensorModule`: the first
  row.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck CategoryTheory.Limits.hasProduct_comp_obj

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- `M ↦ 𝒪_X ⊗_R M` preserves colimits, being a left adjoint. -/
private instance baseRingTensorModule_preservesColimits :
    PreservesColimitsOfSize.{0, 0} (baseRingTensorModule B S hS X φ) :=
  (baseRingTensorModuleAdjunction B S hS X φ).leftAdjoint_preservesColimits

/-- `M ↦ 𝒪_X ⊗_R M` is a left adjoint. -/
private instance baseRingTensorModule_isLeftAdjoint :
    (baseRingTensorModule B S hS X φ).IsLeftAdjoint :=
  (baseRingTensorModuleAdjunction B S hS X φ).isLeftAdjoint

/-- `M ↦ 𝒪_X ⊗_R M` is additive, being a left adjoint between additive categories. -/
instance baseRingTensorModule_additive : (baseRingTensorModule B S hS X φ).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (baseRingTensorModule B S hS X φ) :=
    (baseRingTensorModuleAdjunction B S hS X φ).leftAdjoint_preservesColimits
  have := (baseRingTensorModuleAdjunction B S hS X φ).isLeftAdjoint
  have : (baseRingTensorModule B S hS X φ).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (baseRingTensorModule B S hS X φ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **The second row of the proof of Stacks 0D3F**: for a tower `(M_n)` of `R`-modules with
surjective transition maps, `lim (𝒪_X ⊗_R M_n) ⟶ ∏ 𝒪_X ⊗_R M_n ⟶ ∏ 𝒪_X ⊗_R M_n` is short
exact. -/
theorem shortExact_inverseLimitSequence_baseRingTensorModule (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ => (Msys ⋙ baseRingTensorModule B S hS X φ).obj ⟨n⟩]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X φ)] :
    (inverseLimitSequence (Msys ⋙ baseRingTensorModule B S hS X φ)).ShortExact := by
  have hU : ∀ U : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 U → ∀ n : ℕ,
      Function.Surjective (((Msys ⋙ baseRingTensorModule B S hS X φ).map
        (homOfLE (Nat.le_succ n)).op).val.app (op U)) := by
    intro U hU n
    have : Epi (Msys.map (homOfLE (Nat.le_succ n)).op) :=
      (ModuleCat.epi_iff_surjective _).2 (hsurj n)
    exact surjective_val_app_of_epi_of_isQuasicoherentOnSite
      ((baseRingTensorModule B S hS X φ).map (Msys.map (homOfLE (Nat.le_succ n)).op))
      inferInstance (isQuasicoherentOnSite_baseRingTensorModule B S hS X φ _)
      (isQuasicoherentOnSite_baseRingTensorModule B S hS X φ _) U hU
  have key := Stacks.SheafOfModules.shortExact_inverseLimitSequence_of_surjective
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (IsAffineChart B S hS X.1) (hasEnoughObjects_isAffineChart B S hS X.1)
    (Msys ⋙ baseRingTensorModule B S hS X φ) hU
  exact key

variable {B S hS X} {T : BigFppfOver B S hS}

/-- **The first row of the proof of Stacks 0D3F**: for flat `f : X ⟶ Spec(R)` with `T` affine and
a tower `(M_n)` of `R`-modules with surjective transition maps, `𝒪_X ⊗_R -` carries the short exact
sequence `lim M_n ⟶ ∏ M_n ⟶ ∏ M_n` to a short exact sequence. -/
theorem shortExact_map_inverseLimitSequence_baseRingTensorModule (f : X ⟶ schemeSpace T)
    (hflat : IsFlat B S hS f.hom) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op)) :
    ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).mapShortComplex.obj
      (inverseLimitSequence Msys)).ShortExact := by
  have hM := shortExact_inverseLimitSequence_of_surjective Msys hsurj
  have := hM.epi_g
  have hex := hM.exact.map_of_epi_of_preservesCokernel
    (baseRingTensorModule B S hS X (baseRingHomOfMap f)) inferInstance inferInstance
  have hmono : Mono ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map
      (inverseLimitSequence Msys).f) :=
    mono_baseRingTensorModule_map f hflat hT _ ((ModuleCat.mono_iff_injective _).1 hM.mono_f)
  have hepi : Epi ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map
      (inverseLimitSequence Msys).g) :=
    (baseRingTensorModule B S hS X (baseRingHomOfMap f)).map_epi _
  exact { exact := hex, mono_f := hmono, epi_g := hepi }

end AlgebraicGeometry.Space

end
