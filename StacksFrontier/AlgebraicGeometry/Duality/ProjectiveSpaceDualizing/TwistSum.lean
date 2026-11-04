module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceDualizing.Basic

/-!
# The trace arrow on the shifts of `𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)`

Let `S` be a quasi-compact scheme, let `n = m + 1 ≥ 1`, let `X = ℙⁿ_S` and let
`c : 𝒪_X(-n-1)[n] ⟶ a(𝒪_S)` be the arrow of
`Stacks.Duality.ProjectiveSpaceDualizing.traceDualizing`. The object

  `E = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`

is, over an affine base, a generator of `D_QCoh(𝒪_X)` ([Stacks, Tag 0A9V]), and the proof of
[Stacks, Tag 0A9W] concludes by checking that every shift `E[j]` sees `c` as a bijection. This file
proves that check, for every quasi-compact base: composition with `c` is bijective on
`Hom(E[j], 𝒪_X(-n-1)[n])` for every `j`. It is the summand-wise statement
`Stacks.Duality.ProjectiveSpaceDualizing.bijective_comp_traceDualizing` assembled through the
biproduct and the shift.

## Main definitions

* `Stacks.Duality.ProjectiveSpaceDualizing.twistGenerator`: `E = ⨁_{0 ≤ k ≤ n} 𝒪_X(-k)`, placed
  in degree zero, as an object of `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.ProjectiveSpaceDualizing.bijective_comp_of_iso`,
  `Stacks.Duality.ProjectiveSpaceDualizing.bijective_comp_biproduct` and
  `Stacks.Duality.ProjectiveSpaceDualizing.bijective_comp_iff_map`: bijectivity of composition
  with a fixed morphism is invariant under isomorphism of the source, closed under biproducts of
  the source, and detected by a fully faithful functor.
* `Stacks.Duality.ProjectiveSpaceDualizing.bijective_comp_traceDualizing_shift_twistGenerator`:
  **composition with `c` is bijective on `Hom(E[j], 𝒪_X(-n-1)[n])` for every `j`.**

## References

* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.Duality.ProjectiveSpaceDualizing

/-! ### Bijectivity of composition with a fixed morphism -/

section Composition

variable {D : Type*} [Category D] {M N : D} (c : M ⟶ N)

/-- Bijectivity transfers along equivalences intertwining two maps. -/
private theorem bijective_iff_of_equiv_comm {α α' β β' : Type*} (e : α ≃ β) (e' : α' ≃ β')
    {f : α → α'} {g : β → β'} (h : ∀ x, g (e x) = e' (f x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have : g = e' ∘ f ∘ e.symm := by
    funext y
    simpa using h (e.symm y)
  simp [this]

/-- Bijectivity of composition with `c` on the morphisms out of an object is invariant under
isomorphism of that object. -/
theorem bijective_comp_of_iso {Y Y' : D} (e : Y ≅ Y')
    (h : Function.Bijective (fun s : Y' ⟶ M => s ≫ c)) :
    Function.Bijective (fun s : Y ⟶ M => s ≫ c) := by
  refine (bijective_iff_of_equiv_comm (e.homCongr (Iso.refl M)).symm
    (e.homCongr (Iso.refl N)).symm ?_).1 h
  simp

/-- Bijectivity of composition with `c` on the morphisms out of each summand of a biproduct gives
it on the morphisms out of the biproduct. -/
theorem bijective_comp_biproduct [Preadditive D] {J : Type*} (Y : J → D) [HasBiproduct Y]
    (h : ∀ j, Function.Bijective (fun s : Y j ⟶ M => s ≫ c)) :
    Function.Bijective (fun s : ⨁ Y ⟶ M => s ≫ c) := by
  refine ⟨fun s t hst => biproduct.hom_ext' _ _ fun j => (h j).1 ?_, fun t => ?_⟩
  · simpa using congrArg (biproduct.ι Y j ≫ ·) hst
  · choose s hs using fun j => (h j).2 (biproduct.ι Y j ≫ t)
    exact ⟨biproduct.desc s, biproduct.hom_ext' _ _ fun j => by simpa using hs j⟩

/-- A fully faithful functor detects bijectivity of composition with a morphism. -/
theorem bijective_comp_iff_map {C : Type*} [Category C] {F : C ⥤ D} (hF : F.FullyFaithful)
    {A M N : C} (c : M ⟶ N) :
    Function.Bijective (fun s : A ⟶ M => s ≫ c) ↔
      Function.Bijective (fun t : F.obj A ⟶ F.obj M => t ≫ F.map c) := by
  refine (bijective_iff_of_equiv_comm hF.homEquiv.symm hF.homEquiv.symm ?_).symm
  simp [Functor.FullyFaithful.homEquiv]

end Composition

/-! ### The generator `𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` -/

variable (m : ℕ) (S : Scheme.{u})

/-- A finite direct sum of quasi-coherent modules placed in degree zero lies in `D_QCoh(𝒪_X)`. -/
theorem derivedCategoryB_biproduct_singleFunctor {X : Scheme.{u}} {r : ℕ} (F : Fin r → X.Modules)
    (hF : ∀ k, (F k).IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (⨁ fun k => (DerivedCategory.singleFunctor X.Modules 0).obj (F k)) :=
  (DerivedCategoryB.derivedCategoryB _).prop_of_iso
    (biproduct.isoProduct fun k => (DerivedCategory.singleFunctor X.Modules 0).obj (F k)).symm
    ((DerivedCategoryB.derivedCategoryB _).prop_limit _ fun k =>
      DerivedPushforward.derivedCategoryB_singleFunctor_obj _ (hF k.as))

/-- **`E = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`**, placed in degree zero, as an object of `D_QCoh(𝒪_X)`
for `X = ℙⁿ_S`. Each summand is quasi-coherent and `D_QCoh(𝒪_X)` is closed under finite direct
sums. -/
def twistGenerator : quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) S) :=
  ⟨⨁ fun k : Fin (m + 2) => (DerivedCategory.singleFunctor _ 0).obj
      (twistOver (m + 1) S (-(k : ℤ))),
    derivedCategoryB_biproduct_singleFunctor _ fun _ => inferInstance⟩

variable [CompactSpace S]

/-- **Every shift `E[j]` of `E = 𝒪_X ⊕ ⋯ ⊕ 𝒪_X(-n)` sees `c` as a bijection**: composition with
`c : 𝒪_X(-n-1)[n] ⟶ a(𝒪_S)` is bijective on `Hom(E[j], 𝒪_X(-n-1)[n])`. -/
theorem bijective_comp_traceDualizing_shift_twistGenerator (j : ℤ) :
    Function.Bijective (fun s : (twistGenerator m S)⟦j⟧ ⟶ twistDualizing m S =>
      s ≫ traceDualizing m S) := by
  set P := DerivedCategoryB.derivedCategoryB (A := (projectiveSpaceOver (m + 1) S).Modules)
    (SheafOfModules.isQuasicoherent (projectiveSpaceOver (m + 1) S).ringCatSheaf)
  rw [bijective_comp_iff_map (ObjectProperty.fullyFaithfulι P)]
  let Y : Fin (m + 2) → DerivedCategory (projectiveSpaceOver (m + 1) S).Modules := fun k =>
    (DerivedCategory.singleFunctor _ (-j)).obj (twistOver (m + 1) S (-(k : ℤ)))
  let e : P.ι.obj ((twistGenerator m S)⟦j⟧) ≅ ⨁ Y :=
    (P.ι.commShiftIso j).app (twistGenerator m S) ≪≫
      (shiftFunctor _ j).mapBiproduct _ ≪≫
      biproduct.mapIso fun k =>
        ((DerivedCategory.singleFunctors _).shiftIso j (-j) 0 (by omega)).app _
  refine bijective_comp_of_iso _ e (bijective_comp_biproduct _ Y fun k => ?_)
  exact (bijective_comp_iff_map (ObjectProperty.fullyFaithfulι P) _).1
    (bijective_comp_traceDualizing m S k (by omega) j)

end Stacks.Duality.ProjectiveSpaceDualizing

end
