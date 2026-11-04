module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import Mathlib.Algebra.Category.Ring.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# Global functions agree along a kernel pair

Let `q : yoneda.obj A ⟶ F` be a map from a representable presheaf on the big fppf site of `S`,
with kernel pair `r₁ r₂ : R ⟶ A`. A global function on `A` whose pullbacks along `r₁` and `r₂`
agree has equal pullbacks along any two maps `h₁ h₂ : Z ⟶ A` that become equal after composing
with `q`.

## Main results

* `AlgebraicGeometry.Space.gamma_eq_of_isPullback_kernelPair`: A global function on `A` equalized
  by the kernel pair of `q` is equalized by every pair of maps `Z ⟶ A` equalized by `q`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- If `r₁ r₂ : R ⟶ A` is a kernel pair of `q : yoneda.obj A ⟶ F` and `sA` is a global function
on `A` with equal pullbacks along `r₁` and `r₂`, then `sA` has equal pullbacks along any
`h₁ h₂ : Z ⟶ A` with `yoneda.map h₁ ≫ q = yoneda.map h₂ ≫ q`. -/
theorem gamma_eq_of_isPullback_kernelPair {A R : BigFppfOver B S hS} (q : yoneda.obj A ⟶ F)
    (r₁ r₂ : R ⟶ A) (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) q q)
    (sA : Γ((BigFppfOver.toScheme B S hS).obj A, ⊤))
    (hsA : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map r₁).op).hom sA =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map r₂).op).hom sA)
    {Z : BigFppfOver B S hS} (h₁ h₂ : Z ⟶ A) (hh : yoneda.map h₁ ≫ q = yoneda.map h₂ ≫ q) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h₁).op).hom sA =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h₂).op).hom sA := by
  let Tscheme := BigFppfOver.toScheme B S hS
  obtain ⟨d, hd⟩ := Yoneda.fullyFaithful.map_surjective (hR.lift (yoneda.map h₁) (yoneda.map h₂) hh)
  have hd₁ : d ≫ r₁ = h₁ := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hd, hR.lift_fst])
  have hd₂ : d ≫ r₂ = h₂ := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hd, hR.lift_snd])
  rw [← hd₁, ← hd₂, Functor.map_comp, Functor.map_comp,
    ← gamma_map_comp (Tscheme.map d) (Tscheme.map r₁),
    ← gamma_map_comp (Tscheme.map d) (Tscheme.map r₂), hsA]

end AlgebraicGeometry.Space

end
