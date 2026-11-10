module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceModules
public import StacksFrontier.CategoryTheory.Bicategory.LeftAdjointStrongTrans

/-!
# The Frobenius base change twist is an isomorphism

Let `a ≫ g = g ≫ b` be a commutative square of schemes with `a` and `b` universal
homeomorphisms, and let `ψ : 𝟭 ≅ b_*`.  The base change twist `g^{-1} ⟶ a_* g^{-1}`
(`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist`) is `g^{-1} ψ` followed by the base change
map `g^{-1} b_* ⟶ a_* g^{-1}`, the mate of `b_* g_* ≅ g_* a_*` under `g^{-1} ⊣ g_*`.  As `a_*` and
`b_*` are equivalences (topological invariance of the étale site), that mate is an isomorphism:
its mate under the adjunctions of the equivalences `a_*`, `b_*` is the conjugate of the base change
map, and is visibly invertible.  For the geometric Frobenius `π_Y` and its base change `π̄` this
says that the canonical twist `C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` of the canonical geometric Frobenius
is an isomorphism.  It is the input for the invertibility of `π_X^*` on `Hⁱ_c(X_k̄, -)`, needed
in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves, where a Frobenius weight is the
absolute value of a nonzero eigenvalue.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChangeTwist`.
* `Stacks.EtaleCohomology.isIso_frobeniusBaseChangeTwist`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

section Twist

variable (Λ : Type r) [Ring Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y)
  (w : a ≫ g = g ≫ b)
  (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b)

/-- The identification `b_* g_* ≅ g_* a_*` from `a ≫ g = g ≫ b`, as a square. -/
abbrev etaleModuleDirectImageCompSquare :
    TwoSquare (etaleModuleDirectImage.{u, r} Λ g) (etaleModuleDirectImage.{u, r} Λ a)
      (etaleModuleDirectImage.{u, r} Λ b) (etaleModuleDirectImage.{u, r} Λ g) :=
  TwoSquare.mk _ _ _ _ ((etaleModuleDirectImageComp.{u, r} Λ g b (a ≫ g) w).hom ≫
    (etaleModuleDirectImageComp.{u, r} Λ a g (a ≫ g) rfl).inv)

/-- **The base change twist is `g⁻¹ ψ` followed by the base change map**, the mate of
`b_* g_* ≅ g_* a_*` under `g^{-1} ⊣ g_*`. -/
theorem etaleModuleBaseChangeTwist_app_eq (L : EtaleModules.{u, r} Λ Y) :
    (etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ).app L =
      (etaleModuleInverseImage.{u, r} Λ g).map (ψ.app L) ≫
        ((mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ g)
            (etaleModuleInverseImageAdj.{u, r} Λ g)).symm
          (etaleModuleDirectImageCompSquare Λ g a b w)).app L := by
  rw [etaleModuleBaseChangeTwist_app, Adjunction.homEquiv_counit]
  simp [etaleModuleBaseChangeTwistAdj, mateEquiv_symm_apply]

/-- **The base change twist along universal homeomorphisms is an isomorphism**, when `ψ` is. -/
public theorem isIso_etaleModuleBaseChangeTwist [UniversalHomeomorphism a]
    [UniversalHomeomorphism b] [IsIso ψ] :
    IsIso (etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ) := by
  have := etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism Λ a
  have := etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism Λ b
  have := isIso_mateEquiv_symm_of_isEquivalence (etaleModuleInverseImageAdj.{u, r} Λ g)
    (etaleModuleInverseImageAdj.{u, r} Λ g) (etaleModuleDirectImageCompSquare Λ g a b w)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun L => ?_
  rw [etaleModuleBaseChangeTwist_app_eq]
  infer_instance

end Twist

section Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The canonical Frobenius twist `C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` is an isomorphism.** -/
public instance isIso_frobeniusBaseChangeTwist :
    IsIso (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) :=
  isIso_etaleModuleBaseChangeTwist Λ _ _ _ _ _

end Frobenius

end Stacks.EtaleCohomology

end
