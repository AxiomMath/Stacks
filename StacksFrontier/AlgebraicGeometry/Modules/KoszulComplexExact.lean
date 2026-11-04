module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.KoszulComplexChern
public import StacksFrontier.LinearAlgebra.ExteriorPower.KoszulExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso

/-!
# Exactness of the Koszul complex of a map to the structure sheaf, stalkwise

Let `𝒱` be a sheaf of modules on a space with a sheaf of commutative rings, and `φ : 𝒱 ⟶ 𝒪`. At
a point `x` the stalk of the Koszul complex of `φ` is the Koszul complex of the functional
`φ_x : 𝒱_x ⟶ 𝒪_x` (`SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction`). So
the Koszul complex is exact at `⋀ⁿ⁺¹ 𝒱` as soon as the Koszul complex of every `φ_x` is.

## Main definitions

* `Stacks.KoszulStalk.stalkDual`: the functional `φ_x`.

## Main results

* `Stacks.KoszulStalk.exact_exteriorContraction_of_stalk`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace Stacks.KoszulStalk

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (φ : M ⟶ SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

section Dual

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The functional `φ_x : 𝒱_x ⟶ 𝒪_x`** of a map `φ : 𝒱 ⟶ 𝒪` at a point. -/
def stalkDual (x : ↥X) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk Osharp.obj x) :=
  (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv Osharp x).toLinearMap ∘ₗ
    PresheafOfModules.stalkMapL x φ.val

/-- The value of `φ_x` on a germ is the germ of the value of `φ`. -/
theorem stalkDual_germ (x : ↥X) (W : Opens ↥X) (hx : x ∈ W) (t : M.val.obj (op W)) :
    stalkDual φ x (TopCat.Presheaf.germ M.val.presheaf W x hx t) =
      TopCat.Presheaf.germ Osharp.obj W x hx (SheafOfModules.unitDualApp φ (op W) t) := by
  refine Eq.trans (congrArg (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv
      Osharp x) (PresheafOfModules.stalkMapL_germ x φ.val W hx t)) ?_
  exact Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv_germ Osharp x W hx _

end Dual

variable (A : SheafOfModules.GradedAlgebra.{u, u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)

/-- The short complex `⋀ⁿ⁺² 𝒱 ⟶ ⋀ⁿ⁺¹ 𝒱 ⟶ ⋀ⁿ 𝒱` of the Koszul complex of `φ`. -/
def koszulShortComplex (n : ℕ) :
    ShortComplex (SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  ShortComplex.mk (SheafOfModules.exteriorContraction M A gen hA φ (n + 1))
    (SheafOfModules.exteriorContraction M A gen hA φ n)
    (SheafOfModules.exteriorContraction_comp_exteriorContraction M A gen hA φ n)

/-- **The Koszul complex of `φ` is exact at `⋀ⁿ⁺¹ 𝒱` if it is so at every stalk.** -/
theorem exact_exteriorContraction_of_stalk (n : ℕ)
    (h : ∀ x : ↥X, ∀ z : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(n + 1)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      exteriorPower.contraction (stalkDual φ x) n z = 0 →
        ∃ w, exteriorPower.contraction (stalkDual φ x) (n + 1) w = z) :
    (koszulShortComplex φ A gen hA n).Exact := by
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun w hw => ?_
  have hc : ∀ (k : ℕ) (w : ↑(TopCat.Presheaf.stalk
      (A.piece ((k + 1 : ℕ) : ℤ)).val.presheaf x)),
      SheafOfModules.exteriorPowerStalkEquiv A gen hA k x (PresheafOfModules.stalkMapL x
        (SheafOfModules.exteriorContraction M A gen hA φ k).val w) =
      exteriorPower.contraction (stalkDual φ x) k
        (SheafOfModules.exteriorPowerStalkEquiv A gen hA (k + 1) x w) := fun k w =>
    SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction A gen hA φ k x _
      (stalkDual_germ φ x) w
  have hw' : PresheafOfModules.stalkMapL x
      (SheafOfModules.exteriorContraction M A gen hA φ n).val w = 0 :=
    (Stacks.SheafOfModules.TopWedge.stalkMap_hom_apply
      (SheafOfModules.exteriorContraction M A gen hA φ n) x w).symm.trans hw
  obtain ⟨w', hw''⟩ := h x (SheafOfModules.exteriorPowerStalkEquiv A gen hA (n + 1) x w)
    ((hc n w).symm.trans ((congrArg _ hw').trans (map_zero _)))
  have key := (hc (n + 1)
    ((SheafOfModules.exteriorPowerStalkEquiv A gen hA (n + 1 + 1) x).symm w')).trans
    ((congrArg (exteriorPower.contraction (stalkDual φ x) (n + 1))
      (LinearEquiv.apply_symm_apply _ w')).trans hw'')
  refine ⟨(SheafOfModules.exteriorPowerStalkEquiv A gen hA (n + 1 + 1) x).symm w', ?_⟩
  exact (Stacks.SheafOfModules.TopWedge.stalkMap_hom_apply
    (SheafOfModules.exteriorContraction M A gen hA φ (n + 1)) x _).trans
    ((SheafOfModules.exteriorPowerStalkEquiv A gen hA (n + 1) x).injective key)

end Stacks.KoszulStalk

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.KoszulStalk

variable {X : Scheme.{u}} (V : X.Modules) (φ : V ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- **The Koszul complex of `φ` is exact at `⋀ⁿ⁺¹ 𝒱` when it is so at every stalk.** -/
theorem exactAt_koszulChain_of_stalk (n : ℕ)
    (h : ∀ x : X, ∀ z,
      exteriorPower.contraction (stalkDual (Osharp := X.sheaf) (M := V) φ x) n z = 0 →
        ∃ w, exteriorPower.contraction (stalkDual (Osharp := X.sheaf) (M := V) φ x) (n + 1) w = z) :
    (koszulChain V φ).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  have hex := exact_exteriorContraction_of_stalk (Osharp := X.sheaf) φ (exteriorAlgebra V)
    (exteriorGenerator V) (isExteriorAlgebra_exteriorAlgebra V) n h
  have h1 : (koszulChain V φ).d (n + 2) (n + 1) = koszulContraction V φ (n + 1) :=
    ChainComplex.of_d (fun n => exteriorPower V ((n : ℕ) : ℤ)) (koszulContraction V φ) (n + 1)
  have h2 : (koszulChain V φ).d (n + 1) n = koszulContraction V φ n :=
    ChainComplex.of_d (fun n => exteriorPower V ((n : ℕ) : ℤ)) (koszulContraction V φ) n
  have hsc : (koszulChain V φ).sc' (n + 2) (n + 1) n =
      koszulShortComplex (Osharp := X.sheaf) φ (exteriorAlgebra V) (exteriorGenerator V)
        (isExteriorAlgebra_exteriorAlgebra V) n := by
    change ShortComplex.mk _ _ _ = ShortComplex.mk _ _ _
    congr 1
  rw [hsc]
  exact hex

end AlgebraicGeometry.Scheme.Modules
