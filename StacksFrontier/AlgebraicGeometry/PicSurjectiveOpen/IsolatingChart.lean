module

public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.QuasiFiniteGorenstein
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.PuncturedFreeness

/-!
# Trivializing an invertible module near a point of the complement

Let `U` be an open of a scheme `X`, let `N` be an invertible `𝒪_U`-module and let `x` be a point
outside `U` whose local ring is Noetherian of Krull dimension at most one.  Suppose `x` admits an
*isolating affine chart*: an affine open `V ∋ x` and `f ∈ Γ(X, V)` with `V ⊓ U = X.basicOpen f`.
Then `N` is trivial on the part inside `U` of a smaller neighbourhood of `x`: there is an open
`V' ∋ x` inside `V` carrying a generating section of `N` over `U.ι ⁻¹ᵁ V'`.

## Main results

* `Stacks.PicSurjectiveOpen.exists_generatorSections_of_isolating_chart`: the statement above.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.PicSurjectiveOpen

variable {X : Scheme.{u}} {U : X.Opens}

/-- **An invertible module on an open subscheme is trivial near a point of the complement whose
local ring is Noetherian of dimension at most one.** The point is given with an isolating affine
chart `V`, meaning that the part of `V` inside `U` is the nonvanishing locus of a single
`f ∈ Γ(X, V)`; the conclusion produces a smaller neighbourhood `V'` of the point over whose
intersection with `U` the module has a generating section. -/
theorem exists_generatorSections_of_isolating_chart (N : U.toScheme.Modules)
    [Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf
      (structureSheafRing U.toScheme.toRingedSpace).property N]
    {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V) (hxU : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)] [Ring.KrullDimLE 1 (X.presheaf.stalk x)]
    (f : Γ(X, V)) (hfU : V ⊓ U = X.basicOpen f) :
    ∃ V' : X.Opens, x ∈ V' ∧ V' ≤ V ∧
      Nonempty (Stacks.SheafOfModules.GeneratorSections U.toScheme.toRingedSpace N
        (U.ι ⁻¹ᵁ V')) := by
  classical
  have hBimg : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = X.basicOpen f := by
    rw [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    exact hfU
  have hBle : X.basicOpen f ≤ U := hfU ▸ inf_le_right
  have hAaff : IsAffineOpen (U.ι ⁻¹ᵁ V) :=
    (U.ι.isAffineOpen_iff_of_isOpenImmersion).mp (hBimg ▸ hV.basicOpen f)
  have hxf : x ∉ X.basicOpen f := fun h => hxU (hBle h)
  have hfp : f ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    by_contra h
    exact hxf ((hV.notMem_primeIdealOf_iff_mem_basicOpen ⟨x, hxV⟩ f).mp h)
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  let : Algebra Γ(X, V) Γ(U.toScheme, U.ι ⁻¹ᵁ V) := (U.ι.app V).hom.toAlgebra
  have : IsLocalization.Away f Γ(U.toScheme, U.ι ⁻¹ᵁ V) :=
    hV.isLocalization_of_eq_basicOpen f
      (homOfLE (x := U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) (Set.image_preimage_subset _ _)) hBimg
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have hinv : ∀ W : U.toScheme.Opens, IsAffineOpen W →
      Module.Invertible Γ(U.toScheme, W) Γ(N, W) := fun W hW =>
    (Stacks.Discriminant.isInvertible_iff_forall_module_invertible N).mp ‹_› ⟨W, hW⟩
  have := hinv _ hAaff
  obtain ⟨g, hg, hfree⟩ :=
    Stacks.PuncturedSpectrum.exists_notMem_free_of_isLocalizedModule Γ(X, V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal hfp (X.presheaf.stalk x)
      Γ(U.toScheme, U.ι ⁻¹ᵁ V) Γ(N, U.ι ⁻¹ᵁ V)
  have hgV : X.basicOpen g ≤ V := X.basicOpen_le g
  have hA'A : U.ι ⁻¹ᵁ X.basicOpen g ≤ U.ι ⁻¹ᵁ V := Scheme.Hom.preimage_mono _ hgV
  have hA'basic : U.ι ⁻¹ᵁ X.basicOpen g
      = U.toScheme.basicOpen ((U.ι.app V).hom g) := U.ι.preimage_basicOpen g
  have halg : algebraMap Γ(X, V) Γ(U.toScheme, U.ι ⁻¹ᵁ V) g = (U.ι.app V).hom g := rfl
  let : Algebra Γ(U.toScheme, U.ι ⁻¹ᵁ V) Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g) :=
    (U.toScheme.presheaf.map (homOfLE hA'A).op).hom.toAlgebra
  have : IsLocalization.Away (algebraMap Γ(X, V) Γ(U.toScheme, U.ι ⁻¹ᵁ V) g)
      Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g) := by
    rw [halg]
    exact hAaff.isLocalization_of_eq_basicOpen _ (homOfLE hA'A) hA'basic
  let := moduleOfLE N hA'A
  have : IsScalarTower Γ(U.toScheme, U.ι ⁻¹ᵁ V) Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g)
      Γ(N, U.ι ⁻¹ᵁ X.basicOpen g) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule
      (Submonoid.powers (algebraMap Γ(X, V) Γ(U.toScheme, U.ι ⁻¹ᵁ V) g))
      (restrictₗ N hA'A) := by
    rw [halg]
    exact isLocalizedModule_restrictₗ N hAaff _ hA'basic hA'A
  have hfreeB : Module.Free Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g)
      Γ(N, U.ι ⁻¹ᵁ X.basicOpen g) :=
    hfree Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g) Γ(N, U.ι ⁻¹ᵁ X.basicOpen g) (restrictₗ N hA'A)
  have hA'aff : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen g) := hA'basic ▸ hAaff.basicOpen _
  have := hinv _ hA'aff
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp hfreeB
  have hbij : Function.Bijective
      fun r : Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g) => r • e.symm 1 := by
    have hfun : (fun r : Γ(U.toScheme, U.ι ⁻¹ᵁ X.basicOpen g) => r • e.symm 1) = e.symm := by
      funext r
      rw [← e.symm.map_smul r 1, smul_eq_mul, mul_one]
    rw [hfun]
    exact e.symm.bijective
  exact ⟨X.basicOpen g, (hV.notMem_primeIdealOf_iff_mem_basicOpen ⟨x, hxV⟩ g).mp hg, hgV,
    ⟨generatorSectionsOfBijectiveSmul N hA'aff (e.symm 1) hbij⟩⟩

end Stacks.PicSurjectiveOpen

end
