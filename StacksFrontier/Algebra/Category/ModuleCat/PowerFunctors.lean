module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# The symmetric and exterior power functors on `ModuleCat`

For a commutative ring `B` and `k : ℕ` this file packages the `k`-th symmetric power and the
`k`-th exterior power of a `B`-module as endofunctors of `ModuleCat B`, so that they can be
applied degreewise to a diagram or to a simplicial module by composition.

## Main definitions

* `Stacks.ModuleCat.symPowFunctor`: `M ↦ Symᵏ_B(M)`.
* `Stacks.ModuleCat.extPowFunctor`: `M ↦ ⋀ᵏ_B(M)`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.ModuleCat

universe u

variable (B : Type u) [CommRing B]

/-- The `k`-th symmetric power as an endofunctor of `ModuleCat B`. -/
def symPowFunctor (k : ℕ) : ModuleCat.{u} B ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (SymPow.symmetricPower k B M)
  map f := ModuleCat.ofHom (SymPow.symMap k f.hom)
  map_id M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    change SymPow.symAlgMap (_root_.ModuleCat.Hom.hom (𝟙 M)) (x : SymmetricAlgebra B M) = _
    rw [show _root_.ModuleCat.Hom.hom (𝟙 M) = LinearMap.id from rfl]
    change (SymmetricAlgebra.lift ((SymmetricAlgebra.ι B M).comp LinearMap.id))
      (x : SymmetricAlgebra B M) = _
    rw [LinearMap.comp_id, SymmetricAlgebra.lift_ι]
    rfl
  map_comp {M N P} f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    change SymPow.symAlgMap ((g.hom).comp f.hom) (x : SymmetricAlgebra B M) =
      SymPow.symAlgMap g.hom (SymPow.symAlgMap f.hom (x : SymmetricAlgebra B M))
    have h : (SymPow.symAlgMap ((g.hom).comp f.hom) :
        SymmetricAlgebra B M →ₐ[B] SymmetricAlgebra B P) =
        (SymPow.symAlgMap g.hom).comp (SymPow.symAlgMap f.hom) := by
      refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
      simp [SymPow.symAlgMap_ι]
    exact congrArg (fun F : SymmetricAlgebra B M →ₐ[B] SymmetricAlgebra B P =>
      F (x : SymmetricAlgebra B M)) h

/-- The `k`-th exterior power as an endofunctor of `ModuleCat B`. -/
def extPowFunctor (k : ℕ) : ModuleCat.{u} B ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (⋀[B]^k M)
  map f := ModuleCat.ofHom (exteriorPower.map k f.hom)
  map_id M := by
    refine ModuleCat.hom_ext ?_
    rw [show _root_.ModuleCat.Hom.hom (𝟙 M) = LinearMap.id from rfl]
    simp
  map_comp {M N P} f g := by
    refine ModuleCat.hom_ext ?_
    simp

end Stacks.ModuleCat

end
