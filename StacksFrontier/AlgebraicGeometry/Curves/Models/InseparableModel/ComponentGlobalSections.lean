module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Components
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions

/-!
# A regular model with an inseparable component: the global functions of the exceptional curve

The exceptional curve `(ker jE) ≅ ℙ¹_κ` of the model of `Stacks.Models.InseparableModel` has
`Γ(E, 𝒪) = κ = k(√t)` as a `k`-algebra: a field of degree two over `k`, not separable over `k`.

## Main results

* `Stacks.Models.InseparableModel.globalSections_of_eq_ker_jE`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

/-- **The global functions of the exceptional curve are `κ`.** For the `k`-algebra structure of
any morphism `g : E ⟶ Spec k` lying over the structure morphism of `X`, `Γ(E, 𝒪)` is a field of
degree two over `k` which is not separable over `k`. -/
theorem globalSections_of_eq_ker_jE {I : XR.IdealSheafData} (hI : I = jE.ker)
    (g : I.subscheme ⟶ Spec (.of k))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) = I.subschemeι ≫ X_to_R) :
    letI : Algebra k Γ(I.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    IsField Γ(I.subscheme, ⊤) ∧ Module.finrank k Γ(I.subscheme, ⊤) = 2 ∧
      ¬ Algebra.IsSeparable k Γ(I.subscheme, ⊤) := by
  subst hI
  -- `ℙ¹_κ ≅ E`, and over `Spec k` it is `ℙ¹_κ ⟶ Spec κ ⟶ Spec k`
  let i : P1 κ ≅ jE.ker.subscheme := asIso jE.toImage
  have hmono : Mono (Spec.map (CommRingCat.ofHom (algebraMap R k))) := by
    have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap R k))
      algebraMap_Rk_surjective
    exact ((IsClosedImmersion.iff_isFinite_and_mono _).1 inferInstance).2
  have hig : i.hom ≫ g = P1toSpec κ ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R k))), Category.assoc, hg,
      Category.assoc, ← jE_comp_X_to_R]
    exact jE.toImage_imageι_assoc X_to_R
  -- on global functions, `k ⟶ Γ(E) ⟶ Γ(ℙ¹_κ)` is `k ⟶ κ ⟶ Γ(ℙ¹_κ)`
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ i.hom.appTop =
      CommRingCat.ofHom (algebraMap k κ) ≫ (Scheme.ΓSpecIso (.of κ)).inv ≫
        (P1toSpec κ).appTop := by
    rw [← Scheme.Hom.comp_appTop, hig, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  -- the `k`-algebra isomorphism `Γ(E, 𝒪) ≃ κ`
  let ψ : Γ(jE.ker.subscheme, ⊤) ≃+* κ :=
    (Scheme.Γ.mapIso i.op).commRingCatIsoToRingEquiv.trans
      (Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections κ 1).symm
  let : Algebra k Γ(jE.ker.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hψ : ∀ c : k, ψ (algebraMap k Γ(jE.ker.subscheme, ⊤) c) = algebraMap k κ c := by
    intro c
    change (Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections κ 1).symm
      (i.hom.appTop (algebraMap k Γ(jE.ker.subscheme, ⊤) c)) = _
    rw [RingEquiv.symm_apply_eq]
    exact congrArg (fun f : CommRingCat.of k ⟶ Γ(P1 κ, ⊤) => f.hom c) key
  let ψ' : Γ(jE.ker.subscheme, ⊤) ≃ₐ[k] κ := AlgEquiv.ofRingEquiv hψ
  exact ⟨MulEquiv.isField (Field.toIsField κ) ψ.toMulEquiv,
    ψ'.toLinearEquiv.finrank_eq.trans finrank_κ,
    fun _ => not_isSeparable (AlgEquiv.Algebra.isSeparable ψ')⟩

end Stacks.Models.InseparableModel
