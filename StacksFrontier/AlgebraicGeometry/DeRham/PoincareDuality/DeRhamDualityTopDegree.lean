module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.DeRhamHodgeCechTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationLETop
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationLEBoundary
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCech
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The top-degree de Rham cohomology of a smooth proper scheme

Let `f : X ⟶ S` be a morphism of schemes with `X` Noetherian of dimension at most `d` and of affine
diagonal, whose sheaves of differential forms vanish above degree `d`. Then
`H^{2d}(X, Ωᵈ[-d]) ⟶ H^{2d}_{dR}(X/S)` is bijective as soon as the top differential
`d : Ω^{d-1} ⟶ Ωᵈ` induces zero on `Hᵈ(X, -)` ([Stacks, Tag 0FW6] when `X` is smooth and proper
over a field): the graded pieces `Ωᵉ[-e]`, `e < d`, of `σ^{≤d-1}Ω^•` have no cohomology in degree
`2d` by Grothendieck's vanishing theorem ([Stacks, Tag 02UZ]), and the boundary map
`H^{2d-1}(X, σ^{≤d-1}Ω^•) ⟶ H^{2d}(X, Ωᵈ[-d])` is induced by the top differential.

## Main results

* `AlgebraicGeometry.Scheme.Hom.bijective_hypercohomologyMap_truncLEι_deRham`: the bijectivity,
  read in `σ^{≤d}Ω^• = Ω^•`.

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
* [Stacks Project, Tag 0FW6](https://stacks.math.columbia.edu/tag/0FW6)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (abSections SectionRing)
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cech.Hypercohomology

universe u

namespace Stacks.Cech.Hypercohomology

open scoped Stacks.StandardDerivedModel

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- A morphism of sheaves of modules placed in a degree, composed. -/
theorem singlePlusMapAt_comp {F G H : SheafOfModules.{u} (ringSheaf O)} (φ : F ⟶ G) (ψ : G ⟶ H)
    (a : ℤ) : singlePlusMapAt O (φ ≫ ψ) a = singlePlusMapAt O φ a ≫ singlePlusMapAt O ψ a :=
  ObjectProperty.hom_ext _ ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).map_comp φ ψ)

/-- A composite `a ≫ ψ ≫ b` placed in a degree induces zero on hypercohomology when `ψ` does. -/
theorem hypercohomologyMap_singlePlusMapAt_comp_eq_zero
    {F F' G' G : SheafOfModules.{u} (ringSheaf O)} (a : F ⟶ F') (ψ : F' ⟶ G') (b : G' ⟶ G) (k n : ℤ)
    (h : hypercohomologyMap O (singlePlusMapAt O ψ k) n = 0) :
    hypercohomologyMap O (singlePlusMapAt O (a ≫ ψ ≫ b) k) n = 0 := by
  rw [singlePlusMapAt_comp, singlePlusMapAt_comp, hypercohomologyMap_comp, hypercohomologyMap_comp,
    h, Limits.zero_comp, Limits.comp_zero]

end Stacks.Cech.Hypercohomology

namespace AlgebraicGeometry.Scheme.Hom

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafOfModules.deRhamComplexPlus

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The terms of the de Rham complex in negative degrees vanish. -/
theorem isZero_deRhamPlus_X_of_neg (n : ℤ) (hn : n < 0) : IsZero ((deRhamPlus f).obj.X n) :=
  (SheafOfModules.deRhamComplex (deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).isZero_extend_X
      ComplexShape.embeddingUpNat n
    fun m hm => by
      have : ((m : ℕ) : ℤ) = n := hm
      omega

/-- **The differential of the de Rham complex in integer degrees is the de Rham differential.** -/
theorem deRhamPlus_d (e : ℕ) :
    (deRhamPlus f).obj.d (e : ℤ) ((e + 1 : ℕ) : ℤ) =
      ((SheafOfModules.deRhamComplex (deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).extendXIso
            ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f e = (e : ℤ))).hom ≫
        f.deRhamComplex.d e (e + 1) ≫
        ((SheafOfModules.deRhamComplex (deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).extendXIso
            ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f (e + 1) = ((e + 1 : ℕ) : ℤ))).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

/-- **The top differential induces zero on the hypercohomology of the de Rham terms placed in
degree zero** when it does on the cohomology of the underlying abelian sheaves. -/
theorem hypercohomologyMap_deRhamPlus_d_eq_zero (e : ℕ)
    (h : ((sectionsFunctor X.carrier ⊤).rightDerived (e + 1)).map
      ((_root_.SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0) :
    hypercohomologyMap (inverseImageRingSheaf f)
        (singlePlusMapAt (inverseImageRingSheaf f)
          ((deRhamPlus f).obj.d (e : ℤ) ((e + 1 : ℕ) : ℤ)) 0)
        ((e + 1 : ℕ) : ℤ) = 0 := by
  rw [deRhamPlus_d]
  exact hypercohomologyMap_singlePlusMapAt_comp_eq_zero _ _ _ 0 _
    ((rightDerived_toSheaf_map_eq_zero_iff (inverseImageRingSheaf f)
      (f.deRhamComplex.d e (e + 1)) (e + 1)).1 h)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Grothendieck vanishing for the terms of the de Rham complex**: on a Noetherian scheme of
dimension at most `d`, `Hⁿ(X, Ωᵉ[-e]) = 0` for `n - e > d`. -/
theorem isZero_hypercohomology_deRhamPlus_X (d : ℕ) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (e n : ℤ) (h : (d : ℤ) < n - e) :
    IsZero (hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X e) e) n) := by
  by_cases he : e < 0
  · exact isZero_hypercohomology_singlePlus_of_isZero _ (isZero_deRhamPlus_X_of_neg f e he) e n
  · exact isZero_hypercohomology_singlePlus_of_lt_sub _ _ hdim e (cechComputes_deRhamPlus_X f e)
      ((cechComputesSheaf_deRhamComplexInt_X f e).singlePlus _ 0) h

/-- **The class of the image of a Čech cocycle under the top differential vanishes in
`H^{2d}(X, Ωᵈ[-d])`** when the top differential induces zero on `Hᵈ(X, -)`. -/
theorem cechCocycleClassAt_push_deRhamPlus_d (e : ℕ)
    (hd : ((sectionsFunctor X.carrier ⊤).rightDerived (e + 1)).map
      ((_root_.SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0)
    {J : Type u} (V : J → TopologicalSpace.Opens X.carrier) (hV : ⊤ = ⨆ j, V j)
    (c : CechCochains.Cochain V (abSections ((deRhamPlus f).obj.X (e : ℤ))) (e + 1))
    (hc : CechCochains.cechD V _ (e + 1) c = 0)
    (hpc : CechCochains.cechD V (abSections ((deRhamPlus f).obj.X ((e + 1 : ℕ) : ℤ))) (e + 1)
      (Stacks.Cohomology.CechOne.push V ((_root_.SheafOfModules.toSheaf _).map
        ((deRhamPlus f).obj.d (e : ℤ) ((e + 1 : ℕ) : ℤ))).hom (e + 1) c) = 0) :
    cechCocycleClassAt V hV ((deRhamPlus f).obj.X ((e + 1 : ℕ) : ℤ)) ((e + 1 : ℕ) : ℤ)
      (Stacks.Cohomology.CechOne.push V ((_root_.SheafOfModules.toSheaf _).map
        ((deRhamPlus f).obj.d (e : ℤ) ((e + 1 : ℕ) : ℤ))).hom (e + 1) c) hpc = 0 := by
  have hX := cechComputes_deRhamPlus_X f ((e + 1 : ℕ) : ℤ)
  have hS := (cechComputesSheaf_deRhamComplexInt_X f ((e + 1 : ℕ) : ℤ)).singlePlus _ 0
  let τ := cechTransferEquiv ((e + 1 : ℕ) : ℤ) 0
    (Iso.refl _) hX hS (e + 1)
  refine (map_eq_zero_iff τ τ.injective).1 ?_
  refine (cechTransferEquiv_cechCocycleClassAt ((e + 1 : ℕ) : ℤ) 0 V hV
    (Iso.refl _) hX hS _ hpc).trans
    ((cechCocycleClassAt_congr V hV _ 0 rfl _ _).trans
    ((hypercohomologyMap_cechCocycleClassAt V hV 0
      ((deRhamPlus f).obj.d (e : ℤ) ((e + 1 : ℕ) : ℤ)) c hc).symm.trans ?_))
  exact ConcreteCategory.congr_hom (hypercohomologyMap_deRhamPlus_d_eq_zero f e hd)
    (cechCocycleClassAt V hV ((deRhamPlus f).obj.X (e : ℤ)) 0 c hc)

/-- **`H^{2d}(X, Ωᵈ[-d]) ⟶ H^{2d}_{dR}(X/S)` is bijective**, read in `σ^{≤d}Ω^• = Ω^•`, for `X`
Noetherian of dimension at most `d` whose top differential `Ω^{d-1} ⟶ Ωᵈ` induces zero on
`Hᵈ(X, -)` and whose sheaves of forms vanish above degree `d`. -/
theorem bijective_hypercohomologyMap_truncLEι_deRham (d : ℕ) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hd : ∀ e : ℕ, e + 1 = d → ((sectionsFunctor X.carrier ⊤).rightDerived (e + 1)).map
      ((_root_.SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0) :
    Function.Bijective (hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d)) := by
  have h0 : ∀ n, n < 0 → IsZero ((deRhamPlus f).obj.X n) := isZero_deRhamPlus_X_of_neg f
  cases d with
  | zero =>
    have hz := isZero_hypercohomology_truncLEPlus_of_neg (deRhamPlus f) h0 (-1) (by omega)
    refine bijective_hypercohomologyMap_truncLEι (deRhamPlus f) ((0 : ℕ) : ℤ) (-1) (by omega)
      (-1) (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) (by omega) (hz _) ?_
    intro y
    have hy : y = 0 := (ModuleCat.subsingleton_of_isZero (hz (-1))).elim y 0
    rw [hy, map_zero]
  | succ e =>
    have hz : ∀ p N : ℤ, p + e + 1 < N → IsZero (hypercohomology (inverseImageRingSheaf f)
        (truncLEPlus (inverseImageRingSheaf f) (deRhamPlus f) p) N) := fun p N hN =>
      isZero_hypercohomology_truncLEPlus (deRhamPlus f) h0 _ _ fun e' he' =>
        isZero_hypercohomology_deRhamPlus_X f (e + 1) hdim e' _ (by push_cast; omega)
    refine bijective_hypercohomologyMap_truncLEι (deRhamPlus f) ((e + 1 : ℕ) : ℤ) (e : ℤ)
      (by push_cast; rfl) (((e + 1 : ℕ) : ℤ) + (e : ℤ)) (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))
      (by push_cast; omega) (hz _ _ (by push_cast; omega)) ?_
    intro y
    obtain ⟨z, rfl⟩ := (exact_f_g (inverseImageRingSheaf f)
      (truncLESC (inverseImageRingSheaf f) (deRhamPlus f) (e : ℤ) ((e : ℤ) - 1) (by omega))
      (truncLESC_shortExact (inverseImageRingSheaf f) (deRhamPlus f) (e : ℤ) ((e : ℤ) - 1)
        (by omega))
      _ y).1 ((ModuleCat.subsingleton_of_isZero (hz _ _ (by omega))).elim _ _)
    obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq ((deRhamPlus f).obj.X (e : ℤ))
      (e : ℤ) (cechComputes_deRhamPlus_X f (e : ℤ)) (e + 1) z
    change boundary (inverseImageRingSheaf f)
        (truncLESC (inverseImageRingSheaf f) (deRhamPlus f) ((e + 1 : ℕ) : ℤ) (e : ℤ)
          (by push_cast; rfl))
        (truncLESC_shortExact (inverseImageRingSheaf f) (deRhamPlus f) ((e + 1 : ℕ) : ℤ) (e : ℤ)
          (by push_cast; rfl)) (((e + 1 : ℕ) : ℤ) + (e : ℤ)) (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))
        (by push_cast; omega)
        (hypercohomologyMap (inverseImageRingSheaf f)
          (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) (e : ℤ))
          (((e + 1 : ℕ) : ℤ) + (e : ℤ))
          (cechCocycleClassAt V hV ((deRhamPlus f).obj.X (e : ℤ)) (e : ℤ) c hc)) = 0
    rw [boundary_truncLESC_hypercohomologyMap_truncLEι' V hV (deRhamPlus f) ((e + 1 : ℕ) : ℤ)
      (e : ℤ) (by push_cast; rfl) c hc (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))
      (by push_cast; omega)]
    refine (congrArg _ ?_).trans (smul_zero _)
    exact cechCocycleClassAt_push_deRhamPlus_d f e (hd e rfl) V hV c hc
      (by rw [← Stacks.Cohomology.CechOne.push_cechD, hc, map_zero])

end AlgebraicGeometry.Scheme.Hom

end
