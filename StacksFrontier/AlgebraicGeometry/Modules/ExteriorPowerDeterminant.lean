module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteBiproducts

/-!
# Top exterior powers along a short exact sequence, on a scheme

Let `X` be a scheme and `0 ⟶ ℰ' ⟶ ℰ ⟶ ℰ'' ⟶ 0` a short exact sequence of `𝒪_X`-modules with
`ℰ'` finite locally free of constant rank `r'` and `ℰ''` of constant rank `k + 1`. The canonical
comparison of [Stacks, Tag 0B38] is an isomorphism

`⋀^{r'} ℰ' ⊗ ⋀^{k+1} ℰ'' ≅ ⋀^{r'+k+1} ℰ`.

This file records it at the scheme-level spelling `AlgebraicGeometry.Scheme.Modules.exteriorPower`
of the exterior power, and applies it to the split sequence
`0 ⟶ ℒ ⟶ ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)} ⟶ 0` of a constant family.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.exteriorPowerTensorExteriorPowerIso`: the isomorphism of
  [Stacks, Tag 0B38] for a short exact sequence of modules of constant ranks.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerBiproductSuccIso`: for `ℒ` of rank one,
  `ℒ ⊗ ⋀^{m+1}(ℒ^{⊕ (m+1)}) ≅ ⋀^{m+2}(ℒ^{⊕ (m+2)})`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.shortExact_biproduct_ι_zero`: the sequence
  `0 ⟶ ℒ ⟶ ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)} ⟶ 0` (first summand in, the other summands out) is short
  exact.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **[Stacks, Tag 0B38] on a scheme, in the constant-rank form.** For a short exact sequence
`0 ⟶ ℰ' ⟶ ℰ ⟶ ℰ'' ⟶ 0` of `𝒪_X`-modules with `ℰ'` finite locally free of rank `r'` and `ℰ''`
of rank `k + 1`, the canonical comparison `⋀^{r'} ℰ' ⊗ ⋀^{k+1} ℰ'' ⟶ ⋀^{r'+k+1} ℰ` is an
isomorphism. -/
def exteriorPowerTensorExteriorPowerIso {X : Scheme.{u}} {E' E E'' : X.Modules}
    (f : E' ⟶ E) (g : E ⟶ E'') (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (r' k : ℕ) [hE' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [hE'' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' (k + 1)] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          (exteriorPower E' (r' : ℤ))).obj (exteriorPower E'' ((k + 1 : ℕ) : ℤ))) ≅
      exteriorPower E ((r' + (k + 1) : ℕ) : ℤ) :=
  @asIso _ _ _ _ _ (@Stacks.SheafOfModules.TopWedge.isIso_detComparison _ X.sheaf E' E E''
    (_root_.SheafOfModules.algebras _ E') (_root_.SheafOfModules.algebras _ E)
    (_root_.SheafOfModules.algebras _ E'') f g w hS.exact hS.mono_f hS.epi_g r' k hE' hE'')

section Biproduct

variable {X : Scheme.{u}} (L : X.Modules)

/-- A biproduct over `Fin 1` is its only summand. -/
def biproductFinOneIso : (⨁ fun _ : Fin 1 => L) ≅ L where
  hom := biproduct.π (fun _ : Fin 1 => L) 0
  inv := biproduct.ι (fun _ : Fin 1 => L) 0
  hom_inv_id := biproduct.hom_ext' _ _ fun i => by rw [Subsingleton.elim i 0]; simp
  inv_hom_id := biproduct.ι_π_self _ _

/-- The map `ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)}` forgetting the first summand. -/
def biproductDropFirst (m : ℕ) :
    (⨁ fun _ : Fin (m + 2) => L) ⟶ ⨁ fun _ : Fin (m + 1) => L :=
  biproduct.lift fun j => biproduct.π (fun _ : Fin (m + 2) => L) j.succ

/-- Including the first summand and then forgetting it is zero. -/
theorem biproduct_ι_zero_comp_biproductDropFirst (m : ℕ) :
    biproduct.ι (fun _ : Fin (m + 2) => L) 0 ≫ biproductDropFirst L m = 0 := by
  refine biproduct.hom_ext _ _ fun j => ?_
  simp only [biproductDropFirst, Category.assoc, biproduct.lift_π, zero_comp]
  exact biproduct.ι_π_ne _ (Fin.succ_ne_zero j).symm

/-- The splitting of `0 ⟶ ℒ ⟶ ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)} ⟶ 0` by the first projection and
the inclusion of the remaining summands. -/
def biproductSplitting (m : ℕ) :
    (ShortComplex.mk (biproduct.ι (fun _ : Fin (m + 2) => L) 0) (biproductDropFirst L m)
      (biproduct_ι_zero_comp_biproductDropFirst L m)).Splitting where
  r := biproduct.π (fun _ : Fin (m + 2) => L) 0
  s := biproduct.desc fun j : Fin (m + 1) => biproduct.ι (fun _ : Fin (m + 2) => L) j.succ
  f_r := biproduct.ι_π_self _ _
  s_g := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    simp only [biproductDropFirst, biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π,
      Category.comp_id]
    by_cases h : i = j
    · subst h
      simp
    · rw [biproduct.ι_π_ne _ (fun h' => h (Fin.succ_injective _ h')), biproduct.ι_π_ne _ h]
  id := by
    change biproduct.π (fun _ : Fin (m + 2) => L) 0 ≫ biproduct.ι (fun _ : Fin (m + 2) => L) 0 +
      biproductDropFirst L m ≫
        biproduct.desc (fun j : Fin (m + 1) => biproduct.ι (fun _ : Fin (m + 2) => L) j.succ) =
      𝟙 _
    rw [biproductDropFirst, biproduct.lift_desc, ← biproduct.total, Fin.sum_univ_succ (n := m + 1)]

/-- **The sequence `0 ⟶ ℒ ⟶ ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)} ⟶ 0` is short exact**, the first arrow
including the first summand and the second forgetting it. It is split. -/
theorem shortExact_biproduct_ι_zero (m : ℕ) :
    (ShortComplex.mk (biproduct.ι (fun _ : Fin (m + 2) => L) 0) (biproductDropFirst L m)
      (biproduct_ι_zero_comp_biproductDropFirst L m)).ShortExact :=
  (biproductSplitting L m).shortExact

/-- `ℒ^{⊕ (m+1)}` has rank `m + 1` when `ℒ` has rank one: induction along the split sequences
`0 ⟶ ℒ ⟶ ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)} ⟶ 0`. -/
theorem isFiniteLocallyFreeOfRank_biproduct_const
    [hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] : (m : ℕ) →
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (⨁ fun _ : Fin (m + 1) => L : X.Modules) (m + 1)
  | 0 => SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (biproductFinOneIso L).symm hL
  | m + 1 => Stacks.Chow.GenuineChern.rank_of_iso (r := 1 + (m + 1)) (Iso.refl _) (by omega)
      (Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _
        (shortExact_biproduct_ι_zero L m) 1 (m + 1) hL
        (isFiniteLocallyFreeOfRank_biproduct_const m))

/-- **`ℒ ⊗ ⋀^{m+1}(ℒ^{⊕ (m+1)}) ≅ ⋀^{m+2}(ℒ^{⊕ (m+2)})`** for `ℒ` of rank one: [Stacks, Tag 0B38]
along the split sequence `0 ⟶ ℒ ⟶ ℒ^{⊕ (m+2)} ⟶ ℒ^{⊕ (m+1)} ⟶ 0`, with `⋀¹ ℒ ≅ ℒ`. -/
def exteriorPowerBiproductSuccIso (m : ℕ)
    [hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (exteriorPower (⨁ fun _ : Fin (m + 1) => L) ((m + 1 : ℕ) : ℤ))) ≅
      exteriorPower (⨁ fun _ : Fin (m + 2) => L) ((m + 2 : ℕ) : ℤ) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).mapIso
        (exteriorPowerOneIsoSelf L).symm).app _ ≪≫
    exteriorPowerTensorExteriorPowerIso _ _ _ (shortExact_biproduct_ι_zero L m) 1 m (hE' := hL)
      (hE'' := isFiniteLocallyFreeOfRank_biproduct_const L m) ≪≫
    eqToIso (by rw [show 1 + (m + 1) = m + 2 by omega])

end Biproduct

end AlgebraicGeometry.Scheme.Modules

end
