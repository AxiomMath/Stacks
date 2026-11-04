module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechDifferential
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero
public import StacksFrontier.Homology.Perfect.FibreQuasiIsoSpreading

/-!
# Elements of the base-changed Čech model, read on the base change

Let `φ : A →+* A'`, let `f : X ⟶ Spec A` be separated, let `X'` be the base change of `X` along
`Spec A' ⟶ Spec A` with projection `g : X' ⟶ X`, and let `F` be a quasi-coherent `𝒪_X`-module and
`U` a finite affine open cover of `X`. The base-change isomorphism of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsBaseChange.lean` identifies the
extension of scalars of the `ℤ`-indexed Čech model of `F` with the Čech model of `g^*F` for the
inverse-image cover; in a nonnegative degree `m` the latter is the module of alternating Čech
`m`-cochains of `g^*F`. This file packages the composite as `fibreTransport` and records the two
facts about it that statements about cocycles of a base change need: it commutes with the
differentials, and it carries `1 ⊗ s` to the base-change comparison of alternating Čech cochains
applied to `s`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.fibreTransport`

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.fibreTransport_d_apply`
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.fibreTransport_one_tmul`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {f' : X' ⟶ Spec (.of A')}
  {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The degree-`m` term of the base-changed Čech model, as alternating Čech `m`-cochains of the
base change.** -/
def fibreTransport (m : ℕ) :
    (StacksDraft.Perfect.extendScalarsCx φ (baseAlternatingCechComplex f U hU F)).X (m : ℤ) ≅
      Stacks.Cech.alternatingCechModuleObj f' (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj F) m :=
  HomologicalComplex.Hom.isoApp (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff)
      (m : ℤ) ≪≫
    baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
      ((Scheme.Modules.pullback g).obj F) m

/-- **`fibreTransport` commutes with the differentials.** -/
theorem fibreTransport_d_apply (m : ℕ)
    (x : (StacksDraft.Perfect.extendScalarsCx φ (baseAlternatingCechComplex f U hU F)).X (m : ℤ)) :
    (fibreTransport φ hsq F U hU hUaff (m + 1)).hom
        ((StacksDraft.Perfect.extendScalarsCx φ (baseAlternatingCechComplex f U hU F)).d (m : ℤ)
          ((m + 1 : ℕ) : ℤ) x) =
      (Stacks.Cech.alternatingCechModuleComplex f' (fun i => g ⁻¹ᵁ U i)
          ((Scheme.Modules.pullback g).obj F)).d m (m + 1)
        ((fibreTransport φ hsq F U hU hUaff m).hom x) := by
  set Φ := baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff
  have hc : Φ.hom.f ((m + 1 : ℕ) : ℤ)
      ((StacksDraft.Perfect.extendScalarsCx φ (baseAlternatingCechComplex f U hU F)).d (m : ℤ)
        ((m + 1 : ℕ) : ℤ) x) =
      (baseAlternatingCechComplex f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
        ((Scheme.Modules.pullback g).obj F)).d (m : ℤ) ((m + 1 : ℕ) : ℤ) (Φ.hom.f (m : ℤ) x) :=
    congr($(Φ.hom.comm (m : ℤ) ((m + 1 : ℕ) : ℤ)) x).symm
  have hd := congr($(d_comp_baseAlternatingCechComplexXIso_hom f' (fun i => g ⁻¹ᵁ U i)
    (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F) m) (Φ.hom.f (m : ℤ) x))
  change (baseAlternatingCechComplexXIso f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
      ((Scheme.Modules.pullback g).obj F) (m + 1)).hom (Φ.hom.f ((m + 1 : ℕ) : ℤ) _) = _
  rwa [hc]

/-- **`fibreTransport` on `1 ⊗ s`**: it is the base-change comparison of alternating Čech cochains
applied to the degree identification of `s`. -/
theorem fibreTransport_one_tmul (m : ℕ)
    (s : (baseAlternatingCechComplex f U hU F).X (m : ℤ)) :
    letI : Algebra A A' := φ.toAlgebra
    (fibreTransport φ hsq F U hU hUaff m).hom ((1 : A') ⊗ₜ[A] s) =
      Stacks.Cech.alternatingCochainBaseChangeₗ g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl I) F
        (preimage_eq_preimage_equivRefl g U) φ f f'
        (fun W => Stacks.Cech.baseRingHom_comp_app φ f f' g hsq W) m
        ((baseAlternatingCechComplexXIso f U hU F m).hom s) := by
  let : Algebra A A' := φ.toAlgebra
  have h := congr($(baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso φ hsq F U hU hUaff m)
    ((1 : A') ⊗ₜ[A] s))
  refine h.trans ?_
  have h2 : ((ModuleCat.extendScalars.{u, u, u} φ).map
      (baseAlternatingCechComplexXIso f U hU F m).hom).hom ((1 : A') ⊗ₜ[A] s) =
      (1 : A') ⊗ₜ[A] ((baseAlternatingCechComplexXIso f U hU F m).hom s) := rfl
  exact (congrArg (Stacks.Cech.alternatingCechModuleObjBaseChangeIso g U (fun i => g ⁻¹ᵁ U i)
      (Equiv.refl I) F (preimage_eq_preimage_equivRefl g U) φ f f'
      (fun W => Stacks.Cech.baseRingHom_comp_app φ f f' g hsq W) hsq hUaff m).hom h2).trans
    (Stacks.Cech.alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U _ (Equiv.refl I) F
      (preimage_eq_preimage_equivRefl g U) φ f f' _ hsq hUaff m _)

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
