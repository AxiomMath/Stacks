module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechExplicitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.SmallFreeModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.KernelOfEpi
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `R^q f_* 𝐙/p` over an affine base on which the Čech cohomology of `𝒪_X` is free

Let `f : X ⟶ S` be separated over an affine scheme `S` of characteristic `p`, and let `U` be a
finite cover of `X` by opens whose finite intersections are affine. Suppose that in every degree
the Čech cohomology `Hᵐ(U, 𝒪_X)` is a free `Γ(S)`-module of finite rank. Then in every degree
`Rᵐ f_* 𝐆_a ≅ 𝐆_a^r`, with the Frobenius given by a matrix (`higherDirectImageAdditiveIso`), so
by [Stacks, Tag 0GKU] the Artin–Schreier map `F - 1` induces an epimorphism on `Rᵐ f_* 𝐆_a`
with constructible kernel. The long exact sequence of the Artin–Schreier sequence then
identifies `R^q f_* 𝐙/p` with that kernel, which is therefore constructible.

## Main results

* `Stacks.ArtinSchreier.exists_rightDerived_artinSchreierMap_arrowIso`: on `Rᵐ f_* 𝐆_a` the
  Artin–Schreier map is, up to isomorphism, `F - 1` for a Frobenius matrix on `𝐆_a^r`.
* `Stacks.ArtinSchreier.epi_rightDerived_artinSchreierMap`: the Artin–Schreier map induces an
  epimorphism on `Rᵐ f_* 𝐆_a`.
* `Stacks.ArtinSchreier.isConstructibleAbelianSheaf_rightDerived_constantZMod_of_free`:
  `R^q f_* 𝐙/p` is constructible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [IsSeparated f] {ι : Type} [Finite ι]
  (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hUaff : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffineOpen (inter U x))
  {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

include hU hUaff in
/-- **On `Rᵐ f_* 𝐆_a` the Artin–Schreier map is, up to isomorphism, `F - 1` for a Frobenius
matrix on `𝐆_a^r`**, when `Hᵐ(U, 𝒪_X)` is free of finite rank over `Γ(S)`. -/
theorem exists_rightDerived_artinSchreierMap_arrowIso (m : ℕ)
    [Module.Free Γ(S, ⊤) ((baseCech f U).homology m)]
    [Module.Finite Γ(S, ⊤) ((baseCech f U).homology m)] :
    ∃ (r : ℕ) (a : Fin r → Fin r → Γ(S, ⊤))
      (e : ((etaleAbelianDirectImage.{u, 0} f).rightDerived m).obj (additiveSheaf.{u, 0} X) ≅
        freeAdditiveSheaf S r),
      ((etaleAbelianDirectImage.{u, 0} f).rightDerived m).map
          (artinSchreierMap.{u, 0} X hp (natCast_eq_zero_source f hS)) ≫ e.hom =
        e.hom ≫ (frobMatrixMap S hp hS a - 𝟙 _) := by
  obtain ⟨r, z, hz, hT⟩ := exists_cocycles_isIso f U m
  obtain ⟨a, w, hw⟩ := exists_frobenius_relation f U hp hS z hz hT
  have hT' : QuasiIsoAt (moduleBasisMap f U z hz) m :=
    Stacks.QuasiIsoFromSingle.quasiIsoAt_mkHomFromSingle (baseCech f U) m _ _ hT
  refine ⟨r, a, higherDirectImageAdditiveIso f U hU hUaff z hz hT', ?_⟩
  rw [artinSchreierMap, Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.sub_comp,
    Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    higherDirectImageAdditiveIso_frobenius f U hU hUaff z hz hT' hp hS a w hw]

variable (B : BigEtaleSite.{u}) (hBS : B.Contains S)

include hU hUaff B hBS in
/-- **The Artin–Schreier map induces an epimorphism on `Rᵐ f_* 𝐆_a`.** -/
theorem epi_rightDerived_artinSchreierMap [Fact p.Prime] (m : ℕ)
    [Module.Free Γ(S, ⊤) ((baseCech f U).homology m)]
    [Module.Finite Γ(S, ⊤) ((baseCech f U).homology m)] :
    Epi (((etaleAbelianDirectImage.{u, 0} f).rightDerived m).map
      (artinSchreierMap.{u, 0} X hp (natCast_eq_zero_source f hS))) := by
  obtain ⟨r, a, e, he⟩ := exists_rightDerived_artinSchreierMap_arrowIso f U hU hUaff hp hS m
  have := epi_frobMatrixMap_sub_id B S hBS r hp hS a
  rw [← epi_comp_iff_of_isIso _ e.hom, he]
  exact epi_comp _ _

include hU hUaff hp hS in
/-- **`R^q f_* 𝐙/p` is constructible** over an affine base of characteristic `p` on which the
Čech cohomology of `𝒪_X` for the cover `U` is free of finite rank in every degree. -/
theorem isConstructibleAbelianSheaf_rightDerived_constantZMod_of_free [Fact p.Prime] (q : ℕ)
    (hfree : ∀ m : ℕ, Module.Free Γ(S, ⊤) ((baseCech f U).homology m) ∧
      Module.Finite Γ(S, ⊤) ((baseCech f U).homology m)) :
    IsConstructibleAbelianSheaf B (B.obj S hBS)
      ((SmallEtale.sheafEquiv B S hBS AddCommGrpCat.{u + 1}).inverse.obj
        (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))))) := by
  have hX := natCast_eq_zero_source f hS
  have := fun m => (hfree m).1
  have := fun m => (hfree m).2
  let Δ := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleAbelianDirectImage.{u, 0} f)
  have hepi : ∀ m : ℕ, q = m + 1 → Epi ((Δ.functor m).map
      (constantArtinSchreierSequence.{u, 0} X hp hX).g) := fun m _ =>
    epi_rightDerived_artinSchreierMap f U hU hUaff hp hS B hBS m
  let e1 := Δ.isoKernelMapG (constantArtinSchreierSequence_shortExact.{u, 0} X hp hX) q hepi
  obtain ⟨r, a, e, he⟩ := exists_rightDerived_artinSchreierMap_arrowIso f U hU hUaff hp hS q
  let e2 : kernel ((Δ.functor q).map (constantArtinSchreierSequence.{u, 0} X hp hX).g) ≅
      kernel (frobMatrixMap S hp hS a - 𝟙 _) := kernel.mapIso _ _ e e he
  exact isConstructibleAbelianSheaf_congr B (B.obj S hBS)
    ((SmallEtale.sheafEquiv B S hBS AddCommGrpCat.{u + 1}).inverse.mapIso (e1 ≪≫ e2)).symm
    (isConstructibleAbelianSheaf_kernel_frobMatrixMap_sub_id B S hBS r hp hS a)

end Stacks.ArtinSchreier

end
